import Calculus.Bridge.Vectors
import Calculus.Dynamo.Lang.Denote
import Calculus.Dynamo.Alg.Frontier
import Calculus.Dynamo.Lang.Store
import Mathlib.Tactic.FinCases

/-!
# Differential-testing vectors

**Generated — do not edit.** Emitted by `src/codec/lean.ts` from the shipped TypeScript codecs: each
theorem below is one `encode` this library actually performed, proposed to the model as an
equation. A failure here is a disagreement between `src/codec/codec.ts` and `Calculus.denote`, and the
theorem's name says which vector.
-/

/-! A key function is emitted total on the membership subtype, so a single-declared-name object
binds a `k` it never reads. The gate fails this file on any warning, so the linter is off; the
binder cannot be `_` because a multi-name object *does* read `k.1`. -/
set_option linter.unusedVariables false
/-! A vector's name spells the codec pair it came from, so it carries `__`. -/
set_option linter.style.nameCheck false

namespace Calculus

/-! Each numeral of this module, decided once. -/
def numeral0 : WFNumeral := WFNumeral.of "1.5"
def numeral1 : WFNumeral := WFNumeral.of "1"
def numeral2 : WFNumeral := WFNumeral.of "2.5"
def numeral3 : WFNumeral := WFNumeral.of "2"

/-- The one tactic every vector uses.

    `rfl` alone closes the scalar vectors and none of the map-shaped ones: `M`'s payload is a
    key set with a *function* on it, so the model's answer is `fun k => (c.e (f k)).get _` — stuck
    on the bound key, pointwise equal to the emitted lambda and not definitionally equal to it. The
    gap is closed by `funext` and a case split on the key set, applied to a fixpoint so that a map
    nested inside a map is reached too.

    The three wire-set alternatives are the second surprise. The attribute domain types `SS`/`NS`/`BS` as
    `Finset`s, so their *order* carries no information — but a `Finset` is a `Multiset` with a
    proof, a `Multiset` is a quotient of lists, and two `Quot.mk`s of differently-ordered lists
    are not definitionally equal. This library sorts a set on the way out and the model keeps the
    order it was given, so `rfl` diverges on every set whose two sides disagree about order.
    `decide` settles it, because `Finset` equality at a concrete element type is decidable.

    The two list alternatives split a list into its elements before `rfl` runs. `rfl` on a whole
    list asks the kernel for each element at once, and an object inside the list answers with a
    lookup at a bound key, which `rfl` cannot reduce. After the split, each element is a goal of
    its own, and the map alternative reaches the object.

    The alternatives are ordered as they are because `rfl` first sends the top-level goal, a
    mis-ordered set, and a list that holds an object into an `isDefEq` loop. The loop exhausts the
    heartbeat budget rather than failing. -/
macro "vector" : tactic => `(tactic|
  (refine congrArg some ?_
   repeat' first
     | (refine congrArg (Attr.m _) (funext fun k => ?_)
        obtain ⟨_, hk⟩ := k
        fin_cases hk)
     | (refine congrArg Attr.ss (Subtype.ext ?_); decide)
     | (refine congrArg Attr.ns (Subtype.ext ?_); decide)
     | (refine congrArg Attr.bs (Subtype.ext ?_); decide)
     | (refine congrArg Attr.l ?_)
     | (refine congrArg₂ List.cons ?_ ?_)
     | rfl
     | congr 1))

/-- `scalar_string` -/
theorem scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.string : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello")
    = some (Attr.s "hello") := by
  vector

/-- `scalar_decimal` -/
theorem scalar_decimal :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => ((Scoped.Term.held false (Scoped.Term.number) (Scoped.Term.string) (.decimalText, false) []) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "1.5")
    = some (Attr.n (numeral0)) := by
  vector

/-- `scalar_boolean` -/
theorem scalar_boolean :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.boolean : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.bool true)
    = some (Attr.bool true) := by
  vector

/-- `scalar_binary` -/
theorem scalar_binary :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.binary : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.bin [0, 127, 255])
    = some (Attr.b [0, 127, 255]) := by
  vector

/-- `scalar_null` -/
theorem scalar_null :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.null : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.null)
    = some (Attr.null) := by
  vector

/-- `literal_alternatives` -/
theorem literal_alternatives :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.union [Scoped.Term.literal GroundKind.string "A", Scoped.Term.literal GroundKind.string "B"] : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "B")
    = some (Attr.s "B") := by
  vector

/-- `literal_decimal` -/
theorem literal_decimal :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => ((Scoped.Term.held false (Scoped.Term.union [Scoped.Term.literal GroundKind.number (numeral1), Scoped.Term.literal GroundKind.number (numeral2)]) (Scoped.Term.union [Scoped.Term.literal GroundKind.string "1", Scoped.Term.literal GroundKind.string "2.5"]) (.decimalText, false) []) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "2.5")
    = some (Attr.n (numeral2)) := by
  vector

/-- `literal_non_ascii` -/
theorem literal_non_ascii :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.union [Scoped.Term.literal GroundKind.string "⊥", Scoped.Term.literal GroundKind.string "𝔸"] : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "𝔸")
    = some (Attr.s "𝔸") := by
  vector

/-- `literal_binary` -/
theorem literal_binary :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.literal GroundKind.binary [0, 127, 255] : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.bin [0, 127, 255])
    = some (Attr.b [0, 127, 255]) := by
  vector

/-- `set_of_string` -/
theorem set_of_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.set (Scoped.Term.string) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.strSet (NEFinset.of "b" {"a"}))
    = some (Attr.ss (NEFinset.of "a" {"b"})) := by
  vector

/-- `set_of_literal` -/
theorem set_of_literal :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.set (Scoped.Term.union [Scoped.Term.literal GroundKind.string "a", Scoped.Term.literal GroundKind.string "b"]) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.strSet (NEFinset.of "b" {"a"}))
    = some (Attr.ss (NEFinset.of "a" {"b"})) := by
  vector

/-- `set_of_number` -/
theorem set_of_number :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.set (Scoped.Term.number) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.numSet (NEFinset.of (numeral0) {(numeral3)}))
    = some (Attr.ns (NEFinset.of (numeral0) {(numeral3)})) := by
  vector

/-- `array_of_string` -/
theorem array_of_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.array (Scoped.Term.string) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.arr [Value.str "a", Value.str "b"])
    = some (Attr.l [Attr.s "a", Attr.s "b"]) := by
  vector

/-- `list_prefix_spread` -/
theorem list_prefix_spread :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.tuple [Scoped.Term.string] (some (Scoped.Term.string)) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.arr [Value.str "a", Value.str "b", Value.str "c"])
    = some (Attr.l [Attr.s "a", Attr.s "b", Attr.s "c"]) := by
  vector

/-- `list_spread_suffix` -/
theorem list_spread_suffix :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.list [] (some (Scoped.Term.string)) [Scoped.Term.boolean] : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.arr [Value.str "a", Value.str "b", Value.bool true])
    = some (Attr.l [Attr.s "a", Attr.s "b", Attr.bool true]) := by
  vector

/-- `array_empty` -/
theorem array_empty :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.array (Scoped.Term.string) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.arr [])
    = some (Attr.l []) := by
  vector

/-- `tuple_pair` -/
theorem tuple_pair :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.tuple [Scoped.Term.string, Scoped.Term.boolean] none : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.arr [Value.str "a", Value.bool true])
    = some (Attr.l [Attr.s "a", Attr.bool true]) := by
  vector

/-- `open_of_string` -/
theorem open_of_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.object (Scoped.Body.mk ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)) (some (Scoped.Term.string))) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.map {"a", "b"} (fun k => if k.1 = "a" then Value.str "x" else Value.str "y"))
    = some (Attr.m {"a", "b"} (fun k => if k.1 = "a" then Attr.s "x" else Attr.s "y")) := by
  vector

/-- `open_empty` -/
theorem open_empty :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.object (Scoped.Body.mk ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)) (some (Scoped.Term.string))) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.map ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)))
    = some (Attr.m ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1))) := by
  vector

/-- `object_two_fields` -/
theorem object_two_fields :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.object (Scoped.Body.mk {"a", "b"} (fun k => if k.1 = "a" then Scoped.ObjectSlot.req (Scoped.Term.string) else Scoped.ObjectSlot.req (Scoped.Term.boolean)) none) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.map {"a", "b"} (fun k => if k.1 = "a" then Value.str "x" else Value.bool true))
    = some (Attr.m {"a", "b"} (fun k => if k.1 = "a" then Attr.s "x" else Attr.bool true)) := by
  vector

/-- `object_optional_absent` -/
theorem object_optional_absent :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.object (Scoped.Body.mk {"a", "b"} (fun k => if k.1 = "a" then Scoped.ObjectSlot.req (Scoped.Term.string) else Scoped.ObjectSlot.optional (Scoped.Term.boolean)) none) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.map {"a"} (fun k => Value.str "x"))
    = some (Attr.m {"a"} (fun k => Attr.s "x")) := by
  vector

/-- `object_fallback_present` -/
theorem object_fallback_present :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.object (Scoped.Body.mk {"a"} (fun k => Scoped.ObjectSlot.fill (Scoped.Term.string) (Value.str "stand-in")) none) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.map {"a"} (fun k => Value.str "x"))
    = some (Attr.m {"a"} (fun k => Attr.s "x")) := by
  vector

/-- `object_open` -/
theorem object_open :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.object (Scoped.Body.mk {"a"} (fun k => Scoped.ObjectSlot.req (Scoped.Term.string)) (some (Scoped.Term.boolean))) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.map {"a", "z"} (fun k => if k.1 = "a" then Value.str "x" else Value.bool true))
    = some (Attr.m {"a", "z"} (fun k => if k.1 = "a" then Attr.s "x" else Attr.bool true)) := by
  vector

/-- `object_nested` -/
theorem object_nested :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.object (Scoped.Body.mk {"a"} (fun k => Scoped.ObjectSlot.req (Scoped.Term.object (Scoped.Body.mk {"b"} (fun k => Scoped.ObjectSlot.req (Scoped.Term.string)) none))) none) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.map {"a"} (fun k => Value.map {"b"} (fun k => Value.str "x")))
    = some (Attr.m {"a"} (fun k => Attr.m {"b"} (fun k => Attr.s "x"))) := by
  vector

/-- `open_of_restricted_set` -/
theorem open_of_restricted_set :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.object (Scoped.Body.mk ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)) (some (Scoped.Term.set (Scoped.Term.union [Scoped.Term.literal GroundKind.string "a", Scoped.Term.literal GroundKind.string "b"])))) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.map {"a"} (fun k => Value.strSet (NEFinset.of "a" ∅)))
    = some (Attr.m {"a"} (fun k => Attr.ss (NEFinset.of "a" ∅))) := by
  vector

/-- `object_restricted_rest` -/
theorem object_restricted_rest :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.object (Scoped.Body.mk {"a"} (fun k => Scoped.ObjectSlot.req (Scoped.Term.set (Scoped.Term.union [Scoped.Term.literal GroundKind.string "b", Scoped.Term.literal GroundKind.string "c"]))) (some (Scoped.Term.set (Scoped.Term.union [Scoped.Term.literal GroundKind.string "b", Scoped.Term.literal GroundKind.string "c"])))) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.map {"a", "z"} (fun k => if k.1 = "a" then Value.strSet (NEFinset.of "b" ∅) else Value.strSet (NEFinset.of "c" ∅)))
    = some (Attr.m {"a", "z"} (fun k => if k.1 = "a" then Attr.ss (NEFinset.of "b" ∅) else Attr.ss (NEFinset.of "c" ∅))) := by
  vector

/-- `map_inside_a_list` -/
theorem map_inside_a_list :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.array (Scoped.Term.object (Scoped.Body.mk ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)) (some (Scoped.Term.string)))) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.arr [Value.map {"a"} (fun k => Value.str "x")])
    = some (Attr.l [Attr.m {"a"} (fun k => Attr.s "x")]) := by
  vector

/-- `object_with_a_name_inside_a_list` -/
theorem object_with_a_name_inside_a_list :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.array (Scoped.Term.object (Scoped.Body.mk {"a"} (fun k => Scoped.ObjectSlot.req (Scoped.Term.string)) none)) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.arr [Value.map {"a"} (fun k => Value.str "x")])
    = some (Attr.l [Attr.m {"a"} (fun k => Attr.s "x")]) := by
  vector

/-- `open_object_absent_name_inside_a_list` -/
theorem open_object_absent_name_inside_a_list :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.array (Scoped.Term.object (Scoped.Body.mk {"a", "b"} (fun k => if k.1 = "a" then Scoped.ObjectSlot.req (Scoped.Term.string) else Scoped.ObjectSlot.optional (Scoped.Term.boolean)) (some (Scoped.Term.boolean)))) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.arr [Value.map {"a", "z"} (fun k => if k.1 = "a" then Value.str "x" else Value.bool true)])
    = some (Attr.l [Attr.m {"a", "z"} (fun k => if k.1 = "a" then Attr.s "x" else Attr.bool true)]) := by
  vector

/-- `union_of_two` -/
theorem union_of_two :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.union [Scoped.Term.string, Scoped.Term.boolean] : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.bool true)
    = some (Attr.bool true) := by
  vector

/-- `nullable_null` -/
theorem nullable_null :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.union [Scoped.Term.string, Scoped.Term.null] : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.null)
    = some (Attr.null) := by
  vector

/-- `union_by_literal` -/
theorem union_by_literal :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.union [Scoped.Term.object (Scoped.Body.mk {"kind", "x"} (fun k => if k.1 = "kind" then Scoped.ObjectSlot.req (Scoped.Term.literal GroundKind.string "a") else Scoped.ObjectSlot.req (Scoped.Term.string)) none), Scoped.Term.object (Scoped.Body.mk {"kind", "x"} (fun k => if k.1 = "kind" then Scoped.ObjectSlot.req (Scoped.Term.literal GroundKind.string "b") else Scoped.ObjectSlot.req (Scoped.Term.boolean)) none)] : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.map {"kind", "x"} (fun k => if k.1 = "kind" then Value.str "a" else Value.str "v"))
    = some (Attr.m {"kind", "x"} (fun k => if k.1 = "kind" then Attr.s "a" else Attr.s "v")) := by
  vector

/-- `discriminated_union` -/
theorem discriminated_union :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.union [Scoped.Term.object (Scoped.Body.mk {"kind", "x"} (fun k => if k.1 = "kind" then Scoped.ObjectSlot.req (Scoped.Term.literal GroundKind.string "a") else Scoped.ObjectSlot.req (Scoped.Term.string)) none), Scoped.Term.object (Scoped.Body.mk {"kind", "y"} (fun k => if k.1 = "kind" then Scoped.ObjectSlot.req (Scoped.Term.literal GroundKind.string "b") else Scoped.ObjectSlot.req (Scoped.Term.boolean)) none)] : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.map {"kind", "x"} (fun k => if k.1 = "kind" then Value.str "a" else Value.str "v"))
    = some (Attr.m {"kind", "x"} (fun k => if k.1 = "kind" then Attr.s "a" else Attr.s "v")) := by
  vector

/-- `product_two_objects` -/
theorem product_two_objects :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.object (Scoped.Body.mk {"a", "n"} (fun k => if k.1 = "a" then Scoped.ObjectSlot.req (Scoped.Term.string) else Scoped.ObjectSlot.req (Scoped.Term.boolean)) none) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.map {"a", "n"} (fun k => if k.1 = "a" then Value.str "x" else Value.bool true))
    = some (Attr.m {"a", "n"} (fun k => if k.1 = "a" then Attr.s "x" else Attr.bool true)) := by
  vector

/-- `product_union_object` -/
theorem product_union_object :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.union [Scoped.Term.object (Scoped.Body.mk {"a", "n"} (fun k => if k.1 = "a" then Scoped.ObjectSlot.req (Scoped.Term.string) else Scoped.ObjectSlot.req ((Scoped.Term.held false (Scoped.Term.number) (Scoped.Term.string) (.decimalText, false) []))) none), Scoped.Term.object (Scoped.Body.mk {"b", "n"} (fun k => if k.1 = "b" then Scoped.ObjectSlot.req (Scoped.Term.boolean) else Scoped.ObjectSlot.req ((Scoped.Term.held false (Scoped.Term.number) (Scoped.Term.string) (.decimalText, false) []))) none)] : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.map {"a", "n"} (fun k => if k.1 = "a" then Value.str "x" else Value.str "1"))
    = some (Attr.m {"a", "n"} (fun k => if k.1 = "a" then Attr.s "x" else Attr.n (numeral1))) := by
  vector

/-- `product_three` -/
theorem product_three :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.object (Scoped.Body.mk {"p", "q", "r"} (fun k => if k.1 = "p" then Scoped.ObjectSlot.req (Scoped.Term.string) else if k.1 = "q" then Scoped.ObjectSlot.req (Scoped.Term.boolean) else Scoped.ObjectSlot.req ((Scoped.Term.held false (Scoped.Term.number) (Scoped.Term.string) (.decimalText, false) []))) none) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.map {"p", "q", "r"} (fun k => if k.1 = "p" then Value.str "x" else if k.1 = "q" then Value.bool true else Value.str "1"))
    = some (Attr.m {"p", "q", "r"} (fun k => if k.1 = "p" then Attr.s "x" else if k.1 = "q" then Attr.bool true else Attr.n (numeral1))) := by
  vector

/-- `dunion_two_keys` -/
theorem dunion_two_keys :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.union [Scoped.Term.object (Scoped.Body.mk {"kind", "size", "toy"} (fun k => if k.1 = "kind" then Scoped.ObjectSlot.req (Scoped.Term.literal GroundKind.string "pet") else if k.1 = "size" then Scoped.ObjectSlot.req (Scoped.Term.literal GroundKind.string "small") else Scoped.ObjectSlot.req (Scoped.Term.string)) none), Scoped.Term.object (Scoped.Body.mk {"kind", "size", "pen"} (fun k => if k.1 = "kind" then Scoped.ObjectSlot.req (Scoped.Term.literal GroundKind.string "pet") else if k.1 = "size" then Scoped.ObjectSlot.req (Scoped.Term.literal GroundKind.string "large") else Scoped.ObjectSlot.req (Scoped.Term.string)) none)] : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.map {"kind", "size", "toy"} (fun k => if k.1 = "kind" then Value.str "pet" else if k.1 = "size" then Value.str "small" else Value.str "ball"))
    = some (Attr.m {"kind", "size", "toy"} (fun k => if k.1 = "kind" then Attr.s "pet" else if k.1 = "size" then Attr.s "small" else Attr.s "ball")) := by
  vector

/-- `opaque_map` -/
theorem opaque_map :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.opaq : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.map {"a"} (fun k => Value.str "x"))
    = some (Attr.m {"a"} (fun k => Attr.s "x")) := by
  vector

/-- `lazy_string` -/
theorem lazy_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.string : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "x")
    = some (Attr.s "x") := by
  vector

/-- `recursive_json` -/
theorem recursive_json :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.union [Scoped.Term.string, Scoped.Term.array (Scoped.Term.ref 0)] : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.arr [Value.str "a", Value.arr [Value.str "b", Value.arr []]])
    = some (Attr.l [Attr.s "a", Attr.l [Attr.s "b", Attr.l []]]) := by
  vector

/-- `recursive_json__guarded` — the model's guard accepts this term -/
theorem recursive_json__guarded :
    ((⟨1, fun i => match i with | ⟨0, _⟩ => (Scoped.Graph.Term.union [Scoped.Graph.Term.string, Scoped.Graph.Term.array (Scoped.Graph.Term.ref 0)] : Scoped.Graph.Term 1)⟩ : Graph)).guarded = true := kernel_rfl%

/-- `recursive_tree_optional` -/
theorem recursive_tree_optional :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.object (Scoped.Body.mk {"name", "children"} (fun k => if k.1 = "name" then Scoped.ObjectSlot.req (Scoped.Term.string) else Scoped.ObjectSlot.optional (Scoped.Term.array (Scoped.Term.ref 0))) none) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.map {"name"} (fun k => Value.str "root"))
    = some (Attr.m {"name"} (fun k => Attr.s "root")) := by
  vector

/-- `recursive_tree_optional__guarded` — the model's guard accepts this term -/
theorem recursive_tree_optional__guarded :
    ((⟨1, fun i => match i with | ⟨0, _⟩ => (Scoped.Graph.Term.object (Scoped.Graph.Body.mk {"name", "children"} (fun k => if k.1 = "name" then Scoped.Graph.ObjectSlot.req (Scoped.Graph.Term.string) else Scoped.Graph.ObjectSlot.optional (Scoped.Graph.Term.array (Scoped.Graph.Term.ref 0))) none) : Scoped.Graph.Term 1)⟩ : Graph)).guarded = true := kernel_rfl%

/-- `mutual_scope` -/
theorem mutual_scope :
    (Closed.meaning (libTable noCallers) (⟨2, .snoc (c := 0) (n := 2) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.object (Scoped.Body.mk {"b"} (fun k => Scoped.ObjectSlot.req (Scoped.Term.array (Scoped.Term.ref 1))) none) : Scoped.Term 0 2 0) | ⟨1, _⟩ => (Scoped.Term.union [Scoped.Term.null, Scoped.Term.ref 0] : Scoped.Term 0 2 1)), 0⟩ : Closed)).e
      (Value.map {"b"} (fun k => Value.arr [Value.null, Value.map {"b"} (fun k => Value.arr [])]))
    = some (Attr.m {"b"} (fun k => Attr.l [Attr.null, Attr.m {"b"} (fun k => Attr.l [])])) := by
  vector

/-- `mutual_scope__guarded` — the model's guard accepts this term -/
theorem mutual_scope__guarded :
    ((⟨2, fun i => match i with | ⟨0, _⟩ => (Scoped.Graph.Term.union [Scoped.Graph.Term.null, Scoped.Graph.Term.ref 1] : Scoped.Graph.Term 2) | ⟨1, _⟩ => (Scoped.Graph.Term.object (Scoped.Graph.Body.mk {"b"} (fun k => Scoped.Graph.ObjectSlot.req (Scoped.Graph.Term.array (Scoped.Graph.Term.ref 0))) none) : Scoped.Graph.Term 2)⟩ : Graph)).guarded = true := kernel_rfl%

/-! ## Refusals — neither side writes anything for these

44 of 1764 shown; `scripts/gate.sh` elaborates all
1764. One `kernel_rfl%` each, no comparator and no fuel: the answer is `none`,
which carries no function for the funext gap to open under.
-/

/-- `scalar_string__refuses__scalar_boolean` — refused on both sides -/
theorem scalar_string__refuses__scalar_boolean :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.string : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.bool true) = none := kernel_rfl%

/-- `scalar_decimal__refuses__scalar_string` — refused on both sides -/
theorem scalar_decimal__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => ((Scoped.Term.held false (Scoped.Term.number) (Scoped.Term.string) (.decimalText, false) []) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `scalar_boolean__refuses__scalar_string` — refused on both sides -/
theorem scalar_boolean__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.boolean : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `scalar_binary__refuses__scalar_string` — refused on both sides -/
theorem scalar_binary__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.binary : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `scalar_null__refuses__scalar_string` — refused on both sides -/
theorem scalar_null__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.null : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `literal_alternatives__refuses__scalar_string` — refused on both sides -/
theorem literal_alternatives__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.union [Scoped.Term.literal GroundKind.string "A", Scoped.Term.literal GroundKind.string "B"] : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `literal_decimal__refuses__scalar_string` — refused on both sides -/
theorem literal_decimal__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => ((Scoped.Term.held false (Scoped.Term.union [Scoped.Term.literal GroundKind.number (numeral1), Scoped.Term.literal GroundKind.number (numeral2)]) (Scoped.Term.union [Scoped.Term.literal GroundKind.string "1", Scoped.Term.literal GroundKind.string "2.5"]) (.decimalText, false) []) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `literal_non_ascii__refuses__scalar_string` — refused on both sides -/
theorem literal_non_ascii__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.union [Scoped.Term.literal GroundKind.string "⊥", Scoped.Term.literal GroundKind.string "𝔸"] : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `literal_binary__refuses__scalar_string` — refused on both sides -/
theorem literal_binary__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.literal GroundKind.binary [0, 127, 255] : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `set_of_string__refuses__scalar_string` — refused on both sides -/
theorem set_of_string__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.set (Scoped.Term.string) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `set_of_literal__refuses__scalar_string` — refused on both sides -/
theorem set_of_literal__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.set (Scoped.Term.union [Scoped.Term.literal GroundKind.string "a", Scoped.Term.literal GroundKind.string "b"]) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `set_of_number__refuses__scalar_string` — refused on both sides -/
theorem set_of_number__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.set (Scoped.Term.number) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `array_of_string__refuses__scalar_string` — refused on both sides -/
theorem array_of_string__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.array (Scoped.Term.string) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `list_prefix_spread__refuses__scalar_string` — refused on both sides -/
theorem list_prefix_spread__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.tuple [Scoped.Term.string] (some (Scoped.Term.string)) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `list_spread_suffix__refuses__scalar_string` — refused on both sides -/
theorem list_spread_suffix__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.list [] (some (Scoped.Term.string)) [Scoped.Term.boolean] : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `array_empty__refuses__scalar_string` — refused on both sides -/
theorem array_empty__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.array (Scoped.Term.string) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `tuple_pair__refuses__scalar_string` — refused on both sides -/
theorem tuple_pair__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.tuple [Scoped.Term.string, Scoped.Term.boolean] none : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `open_of_string__refuses__scalar_string` — refused on both sides -/
theorem open_of_string__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.object (Scoped.Body.mk ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)) (some (Scoped.Term.string))) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `open_empty__refuses__scalar_string` — refused on both sides -/
theorem open_empty__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.object (Scoped.Body.mk ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)) (some (Scoped.Term.string))) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `object_two_fields__refuses__scalar_string` — refused on both sides -/
theorem object_two_fields__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.object (Scoped.Body.mk {"a", "b"} (fun k => if k.1 = "a" then Scoped.ObjectSlot.req (Scoped.Term.string) else Scoped.ObjectSlot.req (Scoped.Term.boolean)) none) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `object_optional_absent__refuses__scalar_string` — refused on both sides -/
theorem object_optional_absent__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.object (Scoped.Body.mk {"a", "b"} (fun k => if k.1 = "a" then Scoped.ObjectSlot.req (Scoped.Term.string) else Scoped.ObjectSlot.optional (Scoped.Term.boolean)) none) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `object_fallback_present__refuses__scalar_string` — refused on both sides -/
theorem object_fallback_present__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.object (Scoped.Body.mk {"a"} (fun k => Scoped.ObjectSlot.fill (Scoped.Term.string) (Value.str "stand-in")) none) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `object_open__refuses__scalar_string` — refused on both sides -/
theorem object_open__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.object (Scoped.Body.mk {"a"} (fun k => Scoped.ObjectSlot.req (Scoped.Term.string)) (some (Scoped.Term.boolean))) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `object_nested__refuses__scalar_string` — refused on both sides -/
theorem object_nested__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.object (Scoped.Body.mk {"a"} (fun k => Scoped.ObjectSlot.req (Scoped.Term.object (Scoped.Body.mk {"b"} (fun k => Scoped.ObjectSlot.req (Scoped.Term.string)) none))) none) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `open_of_restricted_set__refuses__scalar_string` — refused on both sides -/
theorem open_of_restricted_set__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.object (Scoped.Body.mk ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)) (some (Scoped.Term.set (Scoped.Term.union [Scoped.Term.literal GroundKind.string "a", Scoped.Term.literal GroundKind.string "b"])))) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `object_restricted_rest__refuses__scalar_string` — refused on both sides -/
theorem object_restricted_rest__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.object (Scoped.Body.mk {"a"} (fun k => Scoped.ObjectSlot.req (Scoped.Term.set (Scoped.Term.union [Scoped.Term.literal GroundKind.string "b", Scoped.Term.literal GroundKind.string "c"]))) (some (Scoped.Term.set (Scoped.Term.union [Scoped.Term.literal GroundKind.string "b", Scoped.Term.literal GroundKind.string "c"])))) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `map_inside_a_list__refuses__scalar_string` — refused on both sides -/
theorem map_inside_a_list__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.array (Scoped.Term.object (Scoped.Body.mk ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)) (some (Scoped.Term.string)))) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `object_with_a_name_inside_a_list__refuses__scalar_string` — refused on both sides -/
theorem object_with_a_name_inside_a_list__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.array (Scoped.Term.object (Scoped.Body.mk {"a"} (fun k => Scoped.ObjectSlot.req (Scoped.Term.string)) none)) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `open_object_absent_name_inside_a_list__refuses__scalar_string` — refused on both sides -/
theorem open_object_absent_name_inside_a_list__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.array (Scoped.Term.object (Scoped.Body.mk {"a", "b"} (fun k => if k.1 = "a" then Scoped.ObjectSlot.req (Scoped.Term.string) else Scoped.ObjectSlot.optional (Scoped.Term.boolean)) (some (Scoped.Term.boolean)))) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `union_of_two__refuses__scalar_binary` — refused on both sides -/
theorem union_of_two__refuses__scalar_binary :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.union [Scoped.Term.string, Scoped.Term.boolean] : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.bin [0, 127, 255]) = none := kernel_rfl%

/-- `nullable_null__refuses__scalar_boolean` — refused on both sides -/
theorem nullable_null__refuses__scalar_boolean :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.union [Scoped.Term.string, Scoped.Term.null] : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.bool true) = none := kernel_rfl%

/-- `union_by_literal__refuses__scalar_string` — refused on both sides -/
theorem union_by_literal__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.union [Scoped.Term.object (Scoped.Body.mk {"kind", "x"} (fun k => if k.1 = "kind" then Scoped.ObjectSlot.req (Scoped.Term.literal GroundKind.string "a") else Scoped.ObjectSlot.req (Scoped.Term.string)) none), Scoped.Term.object (Scoped.Body.mk {"kind", "x"} (fun k => if k.1 = "kind" then Scoped.ObjectSlot.req (Scoped.Term.literal GroundKind.string "b") else Scoped.ObjectSlot.req (Scoped.Term.boolean)) none)] : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `discriminated_union__refuses__scalar_string` — refused on both sides -/
theorem discriminated_union__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.union [Scoped.Term.object (Scoped.Body.mk {"kind", "x"} (fun k => if k.1 = "kind" then Scoped.ObjectSlot.req (Scoped.Term.literal GroundKind.string "a") else Scoped.ObjectSlot.req (Scoped.Term.string)) none), Scoped.Term.object (Scoped.Body.mk {"kind", "y"} (fun k => if k.1 = "kind" then Scoped.ObjectSlot.req (Scoped.Term.literal GroundKind.string "b") else Scoped.ObjectSlot.req (Scoped.Term.boolean)) none)] : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `product_two_objects__refuses__scalar_string` — refused on both sides -/
theorem product_two_objects__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.object (Scoped.Body.mk {"a", "n"} (fun k => if k.1 = "a" then Scoped.ObjectSlot.req (Scoped.Term.string) else Scoped.ObjectSlot.req (Scoped.Term.boolean)) none) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `product_union_object__refuses__scalar_string` — refused on both sides -/
theorem product_union_object__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.union [Scoped.Term.object (Scoped.Body.mk {"a", "n"} (fun k => if k.1 = "a" then Scoped.ObjectSlot.req (Scoped.Term.string) else Scoped.ObjectSlot.req ((Scoped.Term.held false (Scoped.Term.number) (Scoped.Term.string) (.decimalText, false) []))) none), Scoped.Term.object (Scoped.Body.mk {"b", "n"} (fun k => if k.1 = "b" then Scoped.ObjectSlot.req (Scoped.Term.boolean) else Scoped.ObjectSlot.req ((Scoped.Term.held false (Scoped.Term.number) (Scoped.Term.string) (.decimalText, false) []))) none)] : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `product_three__refuses__scalar_string` — refused on both sides -/
theorem product_three__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.object (Scoped.Body.mk {"p", "q", "r"} (fun k => if k.1 = "p" then Scoped.ObjectSlot.req (Scoped.Term.string) else if k.1 = "q" then Scoped.ObjectSlot.req (Scoped.Term.boolean) else Scoped.ObjectSlot.req ((Scoped.Term.held false (Scoped.Term.number) (Scoped.Term.string) (.decimalText, false) []))) none) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `dunion_two_keys__refuses__scalar_string` — refused on both sides -/
theorem dunion_two_keys__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.union [Scoped.Term.object (Scoped.Body.mk {"kind", "size", "toy"} (fun k => if k.1 = "kind" then Scoped.ObjectSlot.req (Scoped.Term.literal GroundKind.string "pet") else if k.1 = "size" then Scoped.ObjectSlot.req (Scoped.Term.literal GroundKind.string "small") else Scoped.ObjectSlot.req (Scoped.Term.string)) none), Scoped.Term.object (Scoped.Body.mk {"kind", "size", "pen"} (fun k => if k.1 = "kind" then Scoped.ObjectSlot.req (Scoped.Term.literal GroundKind.string "pet") else if k.1 = "size" then Scoped.ObjectSlot.req (Scoped.Term.literal GroundKind.string "large") else Scoped.ObjectSlot.req (Scoped.Term.string)) none)] : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `lazy_string__refuses__scalar_boolean` — refused on both sides -/
theorem lazy_string__refuses__scalar_boolean :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.string : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.bool true) = none := kernel_rfl%

/-- `recursive_json__refuses__scalar_boolean` — refused on both sides -/
theorem recursive_json__refuses__scalar_boolean :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.union [Scoped.Term.string, Scoped.Term.array (Scoped.Term.ref 0)] : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.bool true) = none := kernel_rfl%

/-- `recursive_tree__refuses__scalar_string` — refused on both sides -/
theorem recursive_tree__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.object (Scoped.Body.mk {"v", "kids"} (fun k => if k.1 = "v" then Scoped.ObjectSlot.req (Scoped.Term.string) else Scoped.ObjectSlot.req (Scoped.Term.array (Scoped.Term.ref 0))) none) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `recursive_category__refuses__scalar_string` — refused on both sides -/
theorem recursive_category__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.object (Scoped.Body.mk {"name", "children"} (fun k => if k.1 = "name" then Scoped.ObjectSlot.req (Scoped.Term.string) else Scoped.ObjectSlot.optional (Scoped.Term.array (Scoped.Term.ref 0))) none) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `recursive_tree_optional__refuses__scalar_string` — refused on both sides -/
theorem recursive_tree_optional__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.object (Scoped.Body.mk {"name", "children"} (fun k => if k.1 = "name" then Scoped.ObjectSlot.req (Scoped.Term.string) else Scoped.ObjectSlot.optional (Scoped.Term.array (Scoped.Term.ref 0))) none) : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `scalar_number__refuses__scalar_string` — refused on both sides -/
theorem scalar_number__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.number : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `never__refuses__scalar_string` — refused on both sides -/
theorem never__refuses__scalar_string :
    (Closed.meaning (libTable noCallers) (⟨1, .snoc (c := 0) (n := 1) (.nil) (fun i => match i with | ⟨0, _⟩ => (Scoped.Term.never : Scoped.Term 0 1 0)), 0⟩ : Closed)).e
      (Value.str "hello") = none := kernel_rfl%

end Calculus

#assert_axioms_module
