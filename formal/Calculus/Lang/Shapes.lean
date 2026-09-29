import Calculus.Lang.ExactA

/-!
# The shape classes of a universe

A universe is a container: its carrier is the W-type of shapes and positions, and a value's
member is its root shape. Each former lands in one class of root shapes: a primitive, a set, a
list or an object. The classes of distinct formers are disjoint, because the carrier is a
coproduct. So two formers in different classes share no value and no attribute, and the six
disjointness laws on each side are theorems of the classes.

A universe supplies the class of each value and of each attribute, and the class where each of
its formers lands. The class is outside `Sem`, as `PrimAdm` is, because only the meet reads it.
-/

namespace Calculus.Alg

/-- The four formers of the term language, as classes of root shapes. -/
inductive Former where
  | prim | set | list | object
deriving DecidableEq

/-- **The shape classes of a universe**: the former class of each value and of each attribute,
    and the landing fact of each former of the signature on each side. -/
class Shapes (S : Syn) [Sem S] where
  /-- The former class of a value. -/
  former : S.V → Former
  /-- The former class of an attribute. -/
  formerA : Syn.A S → Former
  /-- A primitive writes only primitive values. -/
  prim : ∀ g v, ((Syn.ground g).e v).isSome = true → former v = .prim
  /-- A primitive reads only primitive attributes. -/
  primA : ∀ g a, ((Syn.ground g).p a).isSome = true → formerA a = .prim
  /-- A set lift writes only set values. -/
  set : ∀ L, Syn.set (S := S) = some L → ∀ c v, ((L.lift c).e v).isSome = true → former v = .set
  /-- A set lift reads only set attributes. -/
  setA : ∀ L, Syn.set (S := S) = some L → ∀ c a, ((L.lift c).p a).isSome = true →
    formerA a = .set
  /-- The list prism builds list values. -/
  list : ∀ L, Syn.list (S := S) = some L → ∀ vs, former (L.pV.into vs) = .list
  /-- The list prism builds list attributes. -/
  listA : ∀ L, Syn.list (S := S) = some L → ∀ as, formerA (L.pA.into as) = .list
  /-- The map prism builds object values. -/
  map : ∀ F, Syn.map (S := S) = some F → ∀ m, former (F.mV.into m) = .object
  /-- The map prism builds object attributes. -/
  mapA : ∀ F, Syn.map (S := S) = some F → ∀ m, formerA (F.mA.into m) = .object

namespace Shapes

variable {S : Syn} [Sem S] [Shapes S] {α : Table S} {β : Table S.op}

/-- Two Boolean domains whose classes differ are disjoint. -/
theorem and_false_of_ne {α : Type} {cls : α → Former} {P Q : α → Bool} {i j : Former}
    (hij : i ≠ j) (hP : ∀ x, P x = true → cls x = i) (hQ : ∀ x, Q x = true → cls x = j)
    (x : α) : (P x && Q x) = false := by
  cases hp : P x <;> cases hq : Q x
  · rfl
  · rfl
  · rfl
  · exact absurd ((hP x hp).symm.trans (hQ x hq)) hij

/-! ## The landing facts of the terms -/

section Value
variable [PrimAdm S] {ρ ρ' : List S.C}

/-- A primitive admits only primitive values. -/
theorem adm_prim (g : S.Ground) (v : S.V) (h : Adm α β (.prim g) ρ v = true) :
    former v = .prim :=
  Shapes.prim g v ((PrimAdm.admV_exact g v).mp h)

/-- A set admits only set values. -/
theorem adm_set (t : Term S) (v : S.V) (h : Adm α β (.set t) ρ v = true) : former v = .set := by
  simp only [Adm, denote] at h
  split at h
  · next L hL => exact Shapes.set L hL _ v h
  · exact nomatch h

/-- A list admits only list values. -/
theorem adm_list (pre : List (Term S)) sp suf (v : S.V) (h : Adm α β (.list pre sp suf) ρ v = true) :
    former v = .list := by
  simp only [Adm] at h
  split at h
  · next L hL =>
      split at h
      · next vs hv => rw [L.pV.into_out hv]; exact Shapes.list L hL vs
      · exact nomatch h
  · exact nomatch h

/-- An object admits only object values. -/
theorem adm_object (b : Body S) (v : S.V) (h : Adm α β (.object b) ρ v = true) :
    former v = .object := by
  cases b
  simp only [Adm, AdmBody] at h
  split at h
  · next F hF =>
      split at h
      · next m hm => rw [F.mV.into_out hm]; exact Shapes.map F hF m
      · exact nomatch h
  · exact nomatch h

/-! ## The six disjointness laws, on the write side -/

/-- A primitive and a set share no value. -/
theorem prim_set (g : S.Ground) (t : Term S) v : (Adm α β (.prim g) ρ v && Adm α β (.set t) ρ' v) = false :=
  and_false_of_ne (by decide) (adm_prim g) (adm_set t) v

/-- A primitive and a list share no value. -/
theorem prim_list (g : S.Ground) (pre : List (Term S)) sp suf v :
    (Adm α β (.prim g) ρ v && Adm α β (.list pre sp suf) ρ' v) = false :=
  and_false_of_ne (by decide) (adm_prim g) (adm_list pre sp suf) v

/-- A primitive and an object share no value. -/
theorem prim_obj (g : S.Ground) (b : Body S) v : (Adm α β (.prim g) ρ v && Adm α β (.object b) ρ' v) = false :=
  and_false_of_ne (by decide) (adm_prim g) (adm_object b) v

/-- A set and a list share no value. -/
theorem set_list (t : Term S) pre sp suf v :
    (Adm α β (.set t) ρ v && Adm α β (.list pre sp suf) ρ' v) = false :=
  and_false_of_ne (by decide) (adm_set t) (adm_list pre sp suf) v

/-- A set and an object share no value. -/
theorem set_obj (t : Term S) (b : Body S) v : (Adm α β (.set t) ρ v && Adm α β (.object b) ρ' v) = false :=
  and_false_of_ne (by decide) (adm_set t) (adm_object b) v

/-- A list and an object share no value. -/
theorem list_obj (pre : List (Term S)) sp suf (b : Body S) v :
    (Adm α β (.list pre sp suf) ρ v && Adm α β (.object b) ρ' v) = false :=
  and_false_of_ne (by decide) (adm_list pre sp suf) (adm_object b) v

end Value

section Attr
variable [PrimAdmA S] {ρ ρ' : List S.C}

/-- **The shape classes of the dual**: the attribute classes are the value classes, and each
    landing fact of the stored side is a landing fact of the caller side. -/
instance op : Shapes S.op where
  former := formerA (S := S)
  formerA := former (S := S)
  prim g v h := primA (S := S) g v (by rwa [(readC_R (Car := Mean.Car) S.o (Mean.ground g)).1] at h)
  primA g a h := prim (S := S) g a (by rwa [(readC_R (Car := Mean.Car) S.o (Mean.ground g)).2] at h)
  set L' hL' c a h := by
    obtain ⟨L, hL, rfl⟩ := Option.map_eq_some_iff.mp hL'
    have hR := setAt_R L Mean.d_pos S.o (R_convU (S := S.op) c).symm
    exact setA (S := S) (setAt L S.o) (by simp only [Syn.set, hL, Option.map_some]) _ a
      (by rwa [hR.1] at h)
  setA L' hL' c v h := by
    obtain ⟨L, hL, rfl⟩ := Option.map_eq_some_iff.mp hL'
    have hR := setAt_R L Mean.d_pos S.o (R_convU (S := S.op) c).symm
    exact set (S := S) (setAt L S.o) (by simp only [Syn.set, hL, Option.map_some]) _ v
      (by rwa [hR.2] at h)
  list L' hL' := by
    obtain ⟨L, hL, rfl⟩ := Option.map_eq_some_iff.mp hL'
    exact listA (S := S) (L.at S.o) (by simp only [Syn.list, hL, Option.map_some])
  listA L' hL' := by
    obtain ⟨L, hL, rfl⟩ := Option.map_eq_some_iff.mp hL'
    exact list (S := S) (L.at S.o) (by simp only [Syn.list, hL, Option.map_some])
  map F' hF' := by
    obtain ⟨F, hF, rfl⟩ := Option.map_eq_some_iff.mp hF'
    exact mapA (S := S) (F.at S.o) (by simp only [Syn.map, hF, Option.map_some])
  mapA F' hF' := by
    obtain ⟨F, hF, rfl⟩ := Option.map_eq_some_iff.mp hF'
    exact map (S := S) (F.at S.o) (by simp only [Syn.map, hF, Option.map_some])

/-! ## The six disjointness laws, on the read side: the laws of the dual -/

/-- A primitive and a set share no attribute. -/
theorem prim_setA (g : S.Ground) (t : Term S) c : (AdmA α β (.prim g) ρ c && AdmA α β (.set t) ρ' c) = false :=
  prim_set (S := S.op) g t c

/-- A primitive and a list share no attribute. -/
theorem prim_listA (g : S.Ground) (pre : List (Term S)) sp suf c :
    (AdmA α β (.prim g) ρ c && AdmA α β (.list pre sp suf) ρ' c) = false :=
  prim_list (S := S.op) g pre sp suf c

/-- A primitive and an object share no attribute. -/
theorem prim_objA (g : S.Ground) (b : Body S) c :
    (AdmA α β (.prim g) ρ c && AdmA α β (.object b) ρ' c) = false :=
  prim_obj (S := S.op) g b c

/-- A set and a list share no attribute. -/
theorem set_listA (t : Term S) pre sp suf c :
    (AdmA α β (.set t) ρ c && AdmA α β (.list pre sp suf) ρ' c) = false :=
  set_list (S := S.op) t pre sp suf c

/-- A set and an object share no attribute. -/
theorem set_objA (t : Term S) (b : Body S) c : (AdmA α β (.set t) ρ c && AdmA α β (.object b) ρ' c) = false :=
  set_obj (S := S.op) t b c

/-- A list and an object share no attribute. -/
theorem list_objA (pre : List (Term S)) sp suf (b : Body S) c :
    (AdmA α β (.list pre sp suf) ρ c && AdmA α β (.object b) ρ' c) = false :=
  list_obj (S := S.op) pre sp suf b c

end Attr

end Shapes

end Calculus.Alg
