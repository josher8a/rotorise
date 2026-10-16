import Calculus.Lang.ScopePath
import Calculus.Dynamo.Analysis.ScopeDisjoint

/-!
# The frontier of a path into a closed codec at DynamoDB, and narrowing on the graph

Each vector reduces in the kernel. A frontier is the operation of each frame at the path, or a
refusal. The store refuses a name on a list and a position on a map. A position past the prefix of
a list shape with a suffix is a refusal, because the codec of the position depends on the length.
An entry that a cycle returns to is one entry, so a path past the cycle lands on the entry again. Each
child of a container is an entry, so a vector reads an entry as the operation of its body.

Narrowing keeps each option whose view at the dual meets the view of the clause. The narrowing law
at DynamoDB (`Closed.narrowC_law`) reads the laws of the decision at the dual (`dynLaws`).
-/

namespace Calculus

open Alg (Seg)
open Alg.Scoped (Rooted GFrame narrowC)

/-- **A closed codec at DynamoDB, at its root.** -/
def Closed.rooted (t : Closed) : Rooted dynSig := ⟨t.N, t.scope, t.root⟩

/-- The rooted form keeps the meaning. -/
theorem Closed.rooted_meaning (α : Table) (t : Closed) :
    Alg.Scoped.Rooted.meaning (S := dynSyn) (Alg.tables dynSyn.o α dynTableA) t.rooted = t.meaning α := rfl

/-- **The narrowing law at DynamoDB, over closed codecs.** Take an item that the stored view of
    the clause reads. No option that narrowing drops reads the item. Where each kept option is typed
    and meets its obligations, a write at a path whose frontier the kept options give keeps the item
    readable by the options. -/
theorem Closed.narrowC_law (α : Table) {φ : Closed} {os : List Closed}
    (hty : ∀ x ∈ narrowC (S := dynSyn) .dual φ.rooted (os.map Closed.rooted),
      Alg.Scoped.Closed.Typed (Alg.tables dynSyn.o α dynTableA) x.d ∧
        Alg.Scoped.Closed.Obligations (Alg.tables dynSyn.o α dynTableA) x.d)
    (π : List Seg) (res : List (GFrame dynSig))
    (hat : Alg.atG (GFrame.child (S := dynSyn)) π ((narrowC (S := dynSyn) .dual φ.rooted (os.map Closed.rooted)).map Rooted.frame) =
      some res) (w : Codec)
    (hw : ∀ g ∈ res, ∀ x a, w.e x = some a →
      ((Alg.Scoped.GFrame.sem (S := dynSyn) (Alg.tables dynSyn.o α dynTableA) g).p a).isSome)
    {A A' x a : Attr}
    (hφ : (((Alg.Scoped.Closed.viewToG (Alg.tables dynSyn.o α dynTableA) .dual φ.scope).e
      φ.root).p A).isSome = true)
    (hA : (select (os.map (·.meaning α)) (·.p) A).isSome)
    (hx : w.e x = some a) (hput : Alg.putPath (S := dynSyn) π a A = some A') :
    (∀ y ∈ os.map Closed.rooted, y ∉ narrowC (S := dynSyn) .dual φ.rooted (os.map Closed.rooted) →
        (Alg.Scoped.Rooted.meaning (S := dynSyn) (Alg.tables dynSyn.o α dynTableA) y).p A = none) ∧
      (select (os.map (·.meaning α)) (·.p) A').isSome := by
  have e1 : os.map (·.meaning α) =
      (os.map Closed.rooted).map (Alg.Scoped.Rooted.meaning (S := dynSyn) (Alg.tables dynSyn.o α dynTableA)) := by
    rw [List.map_map]; rfl
  rw [e1] at hA ⊢
  exact Alg.Scoped.narrowC_law (dynLaws .dual) hty π res hat w hw hφ hA hx hput

/-! ## Vectors -/

/-- The operation of a graph term, as a tag: `0` an entry, then each operation in the order of
    `TOp`. -/
private def tagOf {N : Nat} : Alg.Scoped.Graph dynSig N → Nat
  | .leaf _ => 0
  | .node (.prim _) _ => 1
  | .node .opaq _ => 2
  | .node .never _ => 3
  | .node .set _ => 4
  | .node (.list _ _ _) _ => 5
  | .node (.refine _ _) _ => 6
  | .node (.held _ _ _) _ => 7
  | .node (.legacy _) _ => 8
  | .node (.obj _ _ _) _ => 9
  | .node (.union _) _ => 10

/-- The operations of a frontier. An entry reads as the operation of its body, because each child
    of a container is an entry. -/
private def tags (r : Option (List (GFrame dynSig))) : Option (List Nat) :=
  r.map (·.map fun f => match f.t with
    | .leaf j => tagOf (f.d.graph j)
    | t => tagOf t)

/-- A union under `m`, whose option `B` declares no `only`. -/
private abbrev itemM : Closed := ⟨6, fun i => match i with
  | ⟨0, _⟩ => (Scoped.Term.object (Scoped.Body.mk {"m"} (fun _ => .req 1) none) : Scoped.Term 6 0)
  | ⟨1, _⟩ => (Scoped.Term.union [
      Scoped.Term.object (Scoped.Body.mk {"tag", "only"} (fun k => if k.1 = "tag" then
        Scoped.ObjectSlot.req 2 else Scoped.ObjectSlot.req 3) none),
      Scoped.Term.object (Scoped.Body.mk {"tag", "shared"} (fun k => if k.1 = "tag" then
        Scoped.ObjectSlot.req 4 else Scoped.ObjectSlot.req 5) none)] : Scoped.Term 6 1)
  | ⟨2, _⟩ => (Scoped.Term.literal .string "A" : Scoped.Term 6 2)
  | ⟨3, _⟩ => (Scoped.Term.number : Scoped.Term 6 3)
  | ⟨4, _⟩ => (Scoped.Term.literal .string "B" : Scoped.Term 6 4)
  | ⟨5, _⟩ => (Scoped.Term.string : Scoped.Term 6 5), 0⟩

-- the frontier at `m.only` is a number and the bottom: `B` reads maps and refuses `only`
example : tags (Alg.Scoped.Rooted.at (S := dynSyn) itemM.rooted [.name "m", .name "only"]) = some [1, 3] := by decide

-- a name on a list: the store refuses the name on every list, so the frontier is empty
private abbrev itemL : Closed := ⟨3, fun i => match i with
  | ⟨0, _⟩ => (Scoped.Term.object (Scoped.Body.mk {"xs"} (fun _ => .req 1) none) : Scoped.Term 3 0)
  | ⟨1, _⟩ => (Scoped.Term.list [] (some 2) [] : Scoped.Term 3 1)
  | ⟨2, _⟩ => (Scoped.Term.string : Scoped.Term 3 2), 0⟩
example : tags (Alg.Scoped.Rooted.at (S := dynSyn) itemL.rooted [.name "xs", .name "foo"]) = some [] := by decide
-- a position past the prefix with no suffix is the spread
example : tags (Alg.Scoped.Rooted.at (S := dynSyn) itemL.rooted [.name "xs", .pos 7]) = some [1] := by decide
-- a position past the prefix with a suffix is a refusal
private abbrev itemS : Closed := ⟨5, fun i => match i with
  | ⟨0, _⟩ => (Scoped.Term.object (Scoped.Body.mk {"xs"} (fun _ => .req 1) none) : Scoped.Term 5 0)
  | ⟨1, _⟩ => (Scoped.Term.list [2] (some 3) [4] : Scoped.Term 5 1)
  | ⟨2, _⟩ => (Scoped.Term.number : Scoped.Term 5 2)
  | ⟨3, _⟩ => (Scoped.Term.string : Scoped.Term 5 3)
  | ⟨4, _⟩ => (Scoped.Term.boolean : Scoped.Term 5 4), 0⟩
example : tags (Alg.Scoped.Rooted.at (S := dynSyn) itemS.rooted [.name "xs", .pos 1]) = none := by decide
example : tags (Alg.Scoped.Rooted.at (S := dynSyn) itemS.rooted [.name "xs", .pos 0]) = some [1] := by decide

-- the path of no segment is the root entry, an object
example : tags (Alg.Scoped.Rooted.at (S := dynSyn) itemL.rooted []) = some [9] := by decide

-- a recursive codec: `kids.0.v` is `string`, and `kids.0.kids.3` lands on the root entry again
private abbrev tree : Closed := ⟨3, fun i => match i with
  | ⟨0, _⟩ => (Scoped.Term.object (Scoped.Body.mk {"v", "kids"} (fun k =>
      if k.1 = "v" then Scoped.ObjectSlot.req 1 else Scoped.ObjectSlot.req 2) none) : Scoped.Term 3 0)
  | ⟨1, _⟩ => (Scoped.Term.string : Scoped.Term 3 1)
  | ⟨2, _⟩ => (Scoped.Term.list [] (some 0) [] : Scoped.Term 3 2), 0⟩
example : tags (Alg.Scoped.Rooted.at (S := dynSyn) tree.rooted [.name "kids", .pos 0, .name "v"]) = some [1] := by decide
example : tags (Alg.Scoped.Rooted.at (S := dynSyn) tree.rooted [.name "kids", .pos 0, .name "kids", .pos 3]) = some [9] := by decide
example : tags (Alg.Scoped.Rooted.at (S := dynSyn) tree.rooted [.name "kids", .pos 0, .name "kids", .pos 3, .name "v"]) =
    some [1] := by decide

-- an opaque attribute: every path is opaque
private abbrev itemO : Closed := ⟨2, fun i => match i with
  | ⟨0, _⟩ => (Scoped.Term.object (Scoped.Body.mk {"o"} (fun _ => .req 1) none) : Scoped.Term 2 0)
  | ⟨1, _⟩ => (Scoped.Term.opaq : Scoped.Term 2 1), 0⟩
example : tags (Alg.Scoped.Rooted.at (S := dynSyn) itemO.rooted [.name "o", .name "x", .pos 2]) = some [2] := by decide

/-! Narrowing on the graph -/

private abbrev clause (k : String) (t : Scoped.Term 3 1) : Closed := ⟨3, fun i => match i with
  | ⟨0, _⟩ => (Scoped.Term.object (Scoped.Body.mk {k} (fun _ => .req 1) (some 2)) : Scoped.Term 3 0)
  | ⟨1, _⟩ => t
  | ⟨2, _⟩ => (Scoped.Term.opaq : Scoped.Term 3 2), 0⟩
private abbrev two (k v : String) (tk : Scoped.Term 3 1) (tv : Scoped.Term 3 2) : Closed :=
  ⟨3, fun i => match i with
    | ⟨0, _⟩ => (Scoped.Term.object (Scoped.Body.mk {k, v} (fun x => if x.1 = k then
        Scoped.ObjectSlot.req 1 else Scoped.ObjectSlot.req 2) none) : Scoped.Term 3 0)
    | ⟨1, _⟩ => tk
    | ⟨2, _⟩ => tv, 0⟩

private abbrev φA : Closed := clause "tag" (Scoped.Term.literal .string "A")
private abbrev φAB : Closed := clause "tag"
  (Scoped.Term.union [Scoped.Term.literal .string "A", Scoped.Term.literal .string "B"])
private abbrev oA : Closed := two "tag" "x" (Scoped.Term.literal .string "A") Scoped.Term.number
private abbrev oAB : Closed := two "tag" "x"
  (Scoped.Term.union [Scoped.Term.literal .string "A", Scoped.Term.literal .string "B"])
  Scoped.Term.string
private abbrev oB : Closed := two "tag" "y" (Scoped.Term.literal .string "B") Scoped.Term.number
private abbrev oS : Closed := two "tag" "z" Scoped.Term.string Scoped.Term.number

-- narrowing keeps every option that the clause meets
example : (narrowC (S := dynSyn) .dual φA.rooted ([oA, oAB, oB, oS].map Closed.rooted)).length = 3 := by decide
-- on a union whose options pin one tag each, narrowing keeps the option of the tag
example : (narrowC (S := dynSyn) .dual φA.rooted ([oA, oB].map Closed.rooted)).length = 1 := by decide
-- `string('A','B')` keeps the options that can hold `A` or `B`
example : (narrowC (S := dynSyn) .dual φAB.rooted ([oA, oAB, oB, oS].map Closed.rooted)).length = 4 := by decide

end Calculus
