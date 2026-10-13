import Calculus.Dynamo.Lang.Term
import Calculus.Lang.CodecPath

/-!
# The data of a clause

A clause at a union names keys and the pin of each key (`AltClause`). An option answers a clause
through the spec of each declared name (`NameSpec`): whether the caller must write the name, and the
pin of its field (`Pin`). A precondition is a list of conditions (`Cond`), each a test at a path
into the item (`readPath`). Each declaration here reads data, and no term.
-/

namespace Calculus

open Alg (Seg)

/-- **What a name is pinned to**: the adapter word, and the alternatives under the word. The word
    is the generators of a `held` in order. The empty word is the native form, so `decimal` pins
    under `[(.decimalText, false)]` and a literal under `[]`. The word is part of the pin because a
    `held` admits the caller's value and not the literal beneath it: a clause at the same literal
    under another word describes other values. -/
abbrev Pin := Word × Alts

/-- One declared name, as a slice reads it: whether the caller must write the name, and the pin
    of its field.

    `required` is the presence at the caller side, `isReqAt .host`. A fill is required there,
    because a fill is optional on the read alone. -/
structure NameSpec where
  required : Bool
  pin : Option Pin

/-- A declared name's pin lies inside the clause's: the same adapter word, the same base, and
    alternatives that are a subset of the clause's.

    **Containment, not membership.** A name pinned to `a | b` admits values at both, so a clause
    at `a` alone does not describe it.

    Four rows, one per base whose carrier has more than one value. `null` has no row because its
    carrier has one inhabitant, so a clause there would keep every member rather than select
    among them. A name pinned at one base against a clause at another is no match, which is the
    `_` row. -/
def altsSub : Option Pin → Pin → Bool
  | some (w, ⟨.string, x⟩),  (w', ⟨.string, c⟩)  => decide (w = w') && decide (∀ a ∈ x.1.val, a ∈ c.1.val)
  | some (w, ⟨.number, x⟩),  (w', ⟨.number, c⟩)  => decide (w = w') && decide (∀ a ∈ x.1.val, a ∈ c.1.val)
  | some (w, ⟨.boolean, x⟩), (w', ⟨.boolean, c⟩) => decide (w = w') && decide (∀ a ∈ x.1.val, a ∈ c.1.val)
  | some (w, ⟨.binary, x⟩),  (w', ⟨.binary, c⟩)  => decide (w = w') && decide (∀ a ∈ x.1.val, a ∈ c.1.val)
  | _, _ => false

/-- **A clause at union level**: the names it speaks about, and the pin it admits at each.

    No index: a union declares no key set, so the clause carries no proof that the options pin its
    names. `AltClause.keyed` decides that against the options, and a clause that it refuses keeps
    nothing (`AltClause.extract_eq_nil_of_keyed_false`). -/
structure AltClause where
  keys : Finset Name
  pin : {k // k ∈ keys} → Pin

/-- One clause key, answered against one option's spec: the name is declared, the caller must
    write it, and its pin lies inside the clause's.

    Required presence is read because an optional literal name admits the map that omits the
    name, so the option holds values outside every fibre the clause describes, and
    the clause does not describe the option. A fill is required at the caller side, so a fill is
    kept. -/
def litSubAt (s : MapOf NameSpec) (c : AltClause) (k : {k // k ∈ c.keys}) : Bool :=
  match s.at k.1 with
  | some ns => ns.required && altsSub ns.pin (c.pin k)
  | none => false

/-- **The form of a pin**: the adapter word and the base. A pin nests inside a pin of its own form
    only (`altsSub_form`). -/
def pinForm (p : Pin) : Word × GroundKind := (p.1, p.2.1)

/-- A pin inside a clause's pin carries the clause's word, and its alternatives lie in the
    clause's. -/
theorem altsSub_inLs {p : Option Pin} {q : Pin} (h : altsSub p q = true) :
    ∃ w al, p = some (w, al) ∧ w = q.1 ∧
      ∀ v, inLs al.1 al.2 v = true → inLs q.2.1 q.2.2 v = true := by
  obtain _ | ⟨w, ⟨k, x⟩⟩ := p
  · simp [altsSub] at h
  obtain ⟨w', ⟨k', c⟩⟩ := q
  refine ⟨w, ⟨k, x⟩, rfl, ?_⟩
  cases k <;> cases k' <;>
    simp only [altsSub, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at h <;>
    exact ⟨h.1, fun v hv => by
      obtain ⟨y, hy, hyv⟩ := inLs_eq_true.mp hv
      exact inLs_eq_true.mpr ⟨y, h.2 y hy, hyv⟩⟩

/-- A pin inside a clause's pin has the clause's form: `altsSub` compares the word and the base. -/
theorem altsSub_form {p : Option Pin} {q : Pin} (h : altsSub p q = true) :
    ∃ r, p = some r ∧ pinForm r = pinForm q := by
  obtain _ | ⟨w, ⟨k, x⟩⟩ := p
  · simp [altsSub] at h
  obtain ⟨w', ⟨k', c⟩⟩ := q
  refine ⟨(w, ⟨k, x⟩), rfl, ?_⟩
  cases k <;> cases k' <;>
    simp only [altsSub, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at h <;>
    obtain ⟨rfl, -⟩ := h <;> rfl

/-! ## The precondition as data -/

/-- A test that the store evaluates on one stored attribute. -/
inductive Test where
  /-- The attribute is one of the literals, at one base. The list holds at least one literal. -/
  | «in» (k : GroundKind) (x : k.Carrier) (xs : List k.Carrier)
  /-- The attribute has the member. -/
  | type (m : Member)
  /-- The attribute exists. -/
  | «exists»

/-- A condition: a test at a path into the item. A precondition is a list of conditions, and the
    precondition holds where each condition holds. -/
structure Cond where
  path : List Seg
  test : Test

/-- **The attribute at a path into an item**, read with the segment read of the store
    (`Alg.getSeg`), which the write at a path (`Alg.putPath`) also reads. -/
def readPath : List Seg → Attr → Option Attr
  | [], a => some a
  | s :: π, a => (Alg.getSeg (S := dynSyn) s a).bind (readPath π)

/-- The test on an attribute. -/
def Test.eval : Test → Attr → Bool
  | .in k x xs, a => (x :: xs).any fun y => inL k y a
  | .type m, a => decide (a.member = m)
  | .exists, _ => true

/-- **A condition on an item**: the attribute at the path exists, and the test holds on the
    attribute. -/
def Cond.eval (c : Cond) (R : Attr) : Bool :=
  match readPath c.path R with
  | some a => c.test.eval a
  | none => false

/-- The segment read of a name at DynamoDB: the entry of a map, and nothing on any other attribute. -/
theorem getSeg_name (k : String) (a : Attr) :
    Alg.getSeg (S := dynSyn) (.name k) a =
      match a with
      | .m keys g => (⟨keys, g⟩ : MapOf Attr).at k
      | _ => none := by
  cases a <;> rfl

/-- A path read with one more segment reads that segment after the path. -/
theorem readPath_append : ∀ (π : List Seg) (s : Seg) (R : Attr),
    readPath (π ++ [s]) R = (readPath π R).bind (Alg.getSeg (S := dynSyn) s)
  | [], s, R => by cases h : Alg.getSeg (S := dynSyn) s R <;> simp [readPath, h]
  | s' :: π, s, R => by
      simp only [List.cons_append, readPath]
      cases Alg.getSeg (S := dynSyn) s' R <;> simp [readPath_append]

/-- A conjunction over the flattened lists of a traversal holds where each list holds. -/
theorem all_flatten_mapM {X Y : Type} {f : X → Option (List Y)} {p : Y → Bool} :
    ∀ {l : List X} {gss : List (List Y)}, l.mapM f = some gss →
      (gss.flatten.all p = true ↔ ∀ x ∈ l, ∀ ys, f x = some ys → ys.all p = true)
  | [], gss, h => by
      simp only [List.mapM_nil, pure, Option.some.injEq] at h
      subst h; simp
  | x :: l, gss, h => by
      simp only [List.mapM_cons, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨ys, hx, gss', h', rfl⟩ := h
      rw [List.flatten_cons, List.all_append, Bool.and_eq_true, all_flatten_mapM h']
      constructor
      · rintro ⟨h₁, h₂⟩ y hy zs hz
        rcases List.mem_cons.mp hy with rfl | hy
        · rw [hx] at hz; cases hz; exact h₁
        · exact h₂ y hy zs hz
      · intro h
        exact ⟨h x List.mem_cons_self ys hx, fun y hy => h y (List.mem_cons_of_mem _ hy)⟩

/-- A traversal that succeeds gives a value at each element. -/
theorem isSome_of_mapM {X Y : Type} {f : X → Option Y} :
    ∀ {l : List X} {ys : List Y}, l.mapM f = some ys → ∀ x ∈ l, ∃ y, f x = some y
  | [], _, _, x, hx => nomatch hx
  | x :: l, ys, h, z, hz => by
      simp only [List.mapM_cons, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨y, hx, ys', h', rfl⟩ := h
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨y, hx⟩
      · exact isSome_of_mapM h' z hz

end Calculus
