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

/-- **The shape classes of a universe**: the former class of each datum, and the landing fact of
    each former of the signature. The carrier is one, so one class serves values and attributes,
    and each landing fact holds at each orientation. -/
class Shapes (S : Syn) [Sem S] where
  /-- The former class of a datum. -/
  former : S.V → Former
  /-- A primitive moves only primitive data. -/
  prim : ∀ o g v, ((Syn.ground g).f o v).isSome = true → former v = .prim
  /-- A set lift moves only set data. -/
  set : ∀ L, Mean.set (B := S.sig) = some L → ∀ c o v, ((L.lift c).f o v).isSome = true →
    former v = .set
  /-- The list prism builds list data. -/
  list : ∀ L, Mean.list (B := S.sig) = some L → ∀ vs, former (L.p.into vs) = .list
  /-- The map prism builds object data. -/
  map : ∀ F, Mean.map (B := S.sig) = some F → ∀ m, former (F.m.into m) = .object

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
  Shapes.prim S.o g v ((PrimAdm.admV_exact g v).mp h)

/-- A set admits only set values. -/
theorem adm_set (t : Term S) (v : S.V) (h : Adm α β (.set t) ρ v = true) : former v = .set := by
  simp only [Adm, denote, denoteAbs] at h
  split at h
  · next L hL => exact Shapes.set L hL _ S.o v h
  · exact nomatch h

/-- A list admits only list values. -/
theorem adm_list (pre : List (Term S)) sp suf (v : S.V) (h : Adm α β (.list pre sp suf) ρ v = true) :
    former v = .list := by
  simp only [Adm] at h
  split at h
  · next L hL =>
      split at h
      · next vs hv => rw [L.p.into_out hv]; exact Shapes.list L hL vs
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
      · next m hm => rw [F.m.into_out hm]; exact Shapes.map F hF m
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

/-- **The shape classes of the dual are the shape classes**: the carrier and the codecs are the
    same, and each landing fact holds at each orientation. -/
instance op : Shapes S.op where
  former := former (S := S)
  prim := prim (S := S)
  set := set (S := S)
  list := list (S := S)
  map := map (S := S)

end Attr

end Shapes

end Calculus.Alg
