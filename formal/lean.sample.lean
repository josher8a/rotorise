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

/-- The one tactic every vector uses.

    `rfl` alone closes the scalar vectors and none of the map-shaped ones: `M`'s payload is a
    key set with a *function* on it, so the model's answer is `fun k => (c.e (f k)).get _` — stuck
    on the bound key, pointwise equal to the emitted lambda and not definitionally equal to it. The
    gap is closed by `funext` and a case split on the key set, applied to a fixpoint so that a map
    nested inside a map is reached too.

    The three wire-set alternatives are the second surprise. §1 types `SS`/`NS`/`BS` as
    `Finset`s, so their *order* carries no information — but a `Finset` is a `Multiset` with a
    proof, a `Multiset` is a quotient of lists, and two `Quot.mk`s of differently-ordered lists
    are not definitionally equal. This library sorts a set on the way out and the model keeps the
    order it was given, so `rfl` diverges on every set whose two sides disagree about order.
    `decide` settles it, because `Finset` equality at a concrete element type is decidable.

    The alternatives are ordered as they are because `rfl` first sends both the top-level goal and
    a mis-ordered set into an `isDefEq` loop that exhausts the heartbeat budget rather than
    failing. -/
macro "vector" : tactic => `(tactic|
  (refine congrArg some ?_
   repeat' first
     | (refine congrArg (Attr.m _) (funext fun k => ?_)
        obtain ⟨_, hk⟩ := k
        fin_cases hk)
     | (refine congrArg Attr.ss (Subtype.ext ?_); decide)
     | (refine congrArg Attr.ns (Subtype.ext ?_); decide)
     | (refine congrArg Attr.bs (Subtype.ext ?_); decide)
     | rfl
     | congr 1))

/-- `scalar_string` -/
theorem scalar_string :
    (denote (Term.string)).e
      (Value.str "hello")
    = some (Attr.s "hello") := by
  vector

/-- `scalar_decimal` -/
theorem scalar_decimal :
    (denote ((Term.held (Term.number) (Term.string) numeralOfStoredText textOfNumeral))).e
      (Value.str "1.5")
    = some (Attr.n (WFNumeral.of "1.5")) := by
  vector

/-- `scalar_boolean` -/
theorem scalar_boolean :
    (denote (Term.boolean)).e
      (Value.bool true)
    = some (Attr.bool true) := by
  vector

/-- `scalar_binary` -/
theorem scalar_binary :
    (denote (Term.binary)).e
      (Value.bin [0, 127, 255])
    = some (Attr.b [0, 127, 255]) := by
  vector

/-- `scalar_null` -/
theorem scalar_null :
    (denote (Term.null)).e
      (Value.null)
    = some (Attr.null) := by
  vector

/-- `literal_alternatives` -/
theorem literal_alternatives :
    (denote (Term.union [Term.literal GroundKind.string "A", Term.literal GroundKind.string "B"])).e
      (Value.str "B")
    = some (Attr.s "B") := by
  vector

/-- `literal_decimal` -/
theorem literal_decimal :
    (denote ((Term.held (Term.union [Term.literal GroundKind.number (WFNumeral.of "1"), Term.literal GroundKind.number (WFNumeral.of "2.5")]) (Term.union [Term.literal GroundKind.string "1", Term.literal GroundKind.string "2.5"]) numeralOfStoredText textOfNumeral))).e
      (Value.str "2.5")
    = some (Attr.n (WFNumeral.of "2.5")) := by
  vector

/-- `literal_non_ascii` -/
theorem literal_non_ascii :
    (denote (Term.union [Term.literal GroundKind.string "⊥", Term.literal GroundKind.string "𝔸"])).e
      (Value.str "𝔸")
    = some (Attr.s "𝔸") := by
  vector

/-- `literal_binary` -/
theorem literal_binary :
    (denote (Term.literal GroundKind.binary [0, 127, 255])).e
      (Value.bin [0, 127, 255])
    = some (Attr.b [0, 127, 255]) := by
  vector

/-- `set_of_string` -/
theorem set_of_string :
    (denote (Term.set (Term.string))).e
      (Value.strSet (NEFinset.of "b" {"a"}))
    = some (Attr.ss (NEFinset.of "a" {"b"})) := by
  vector

/-- `set_of_literal` -/
theorem set_of_literal :
    (denote (Term.set (Term.union [Term.literal GroundKind.string "a", Term.literal GroundKind.string "b"]))).e
      (Value.strSet (NEFinset.of "b" {"a"}))
    = some (Attr.ss (NEFinset.of "a" {"b"})) := by
  vector

/-- `set_of_number` -/
theorem set_of_number :
    (denote (Term.set (Term.number))).e
      (Value.numSet (NEFinset.of (WFNumeral.of "1.5") {(WFNumeral.of "2")}))
    = some (Attr.ns (NEFinset.of (WFNumeral.of "1.5") {(WFNumeral.of "2")})) := by
  vector

/-- `array_of_string` -/
theorem array_of_string :
    (denote (Term.array (Term.string))).e
      (Value.arr [Value.str "a", Value.str "b"])
    = some (Attr.l [Attr.s "a", Attr.s "b"]) := by
  vector

/-- `list_prefix_spread` -/
theorem list_prefix_spread :
    (denote (Term.tuple [Term.string] (some (Term.string)))).e
      (Value.arr [Value.str "a", Value.str "b", Value.str "c"])
    = some (Attr.l [Attr.s "a", Attr.s "b", Attr.s "c"]) := by
  vector

/-- `list_spread_suffix` -/
theorem list_spread_suffix :
    (denote (Term.list [] (some (Term.string)) [Term.boolean])).e
      (Value.arr [Value.str "a", Value.str "b", Value.bool true])
    = some (Attr.l [Attr.s "a", Attr.s "b", Attr.bool true]) := by
  vector

/-- `array_empty` -/
theorem array_empty :
    (denote (Term.array (Term.string))).e
      (Value.arr [])
    = some (Attr.l []) := by
  vector

/-- `tuple_pair` -/
theorem tuple_pair :
    (denote (Term.tuple [Term.string, Term.boolean] none)).e
      (Value.arr [Value.str "a", Value.bool true])
    = some (Attr.l [Attr.s "a", Attr.bool true]) := by
  vector

/-- `open_of_string` -/
theorem open_of_string :
    (denote (Term.object (Body.mk ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)) (some (Term.string))))).e
      (Value.map {"a", "b"} (fun k => if k.1 = "a" then Value.str "x" else Value.str "y"))
    = some (Attr.m {"a", "b"} (fun k => if k.1 = "a" then Attr.s "x" else Attr.s "y")) := by
  vector

/-- `open_empty` -/
theorem open_empty :
    (denote (Term.object (Body.mk ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)) (some (Term.string))))).e
      (Value.map ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)))
    = some (Attr.m ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1))) := by
  vector

/-- `object_two_fields` -/
theorem object_two_fields :
    (denote (Term.object (Body.mk {"a", "b"} (fun k => if k.1 = "a" then ObjectSlot.req (Term.string) else ObjectSlot.req (Term.boolean)) none))).e
      (Value.map {"a", "b"} (fun k => if k.1 = "a" then Value.str "x" else Value.bool true))
    = some (Attr.m {"a", "b"} (fun k => if k.1 = "a" then Attr.s "x" else Attr.bool true)) := by
  vector

/-- `object_optional_absent` -/
theorem object_optional_absent :
    (denote (Term.object (Body.mk {"a", "b"} (fun k => if k.1 = "a" then ObjectSlot.req (Term.string) else ObjectSlot.optional (Term.boolean)) none))).e
      (Value.map {"a"} (fun k => Value.str "x"))
    = some (Attr.m {"a"} (fun k => Attr.s "x")) := by
  vector

/-- `object_open` -/
theorem object_open :
    (denote (Term.object (Body.mk {"a"} (fun k => ObjectSlot.req (Term.string)) (some (Term.boolean))))).e
      (Value.map {"a", "z"} (fun k => if k.1 = "a" then Value.str "x" else Value.bool true))
    = some (Attr.m {"a", "z"} (fun k => if k.1 = "a" then Attr.s "x" else Attr.bool true)) := by
  vector

/-- `object_nested` -/
theorem object_nested :
    (denote (Term.object (Body.mk {"a"} (fun k => ObjectSlot.req (Term.object (Body.mk {"b"} (fun k => ObjectSlot.req (Term.string)) none))) none))).e
      (Value.map {"a"} (fun k => Value.map {"b"} (fun k => Value.str "x")))
    = some (Attr.m {"a"} (fun k => Attr.m {"b"} (fun k => Attr.s "x"))) := by
  vector

/-- `open_of_restricted_set` -/
theorem open_of_restricted_set :
    (denote (Term.object (Body.mk ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)) (some (Term.set (Term.union [Term.literal GroundKind.string "a", Term.literal GroundKind.string "b"])))))).e
      (Value.map {"a"} (fun k => Value.strSet (NEFinset.of "a" ∅)))
    = some (Attr.m {"a"} (fun k => Attr.ss (NEFinset.of "a" ∅))) := by
  vector

/-- `object_restricted_rest` -/
theorem object_restricted_rest :
    (denote (Term.object (Body.mk {"a"} (fun k => ObjectSlot.req (Term.set (Term.union [Term.literal GroundKind.string "b", Term.literal GroundKind.string "c"]))) (some (Term.set (Term.union [Term.literal GroundKind.string "b", Term.literal GroundKind.string "c"])))))).e
      (Value.map {"a", "z"} (fun k => if k.1 = "a" then Value.strSet (NEFinset.of "b" ∅) else Value.strSet (NEFinset.of "c" ∅)))
    = some (Attr.m {"a", "z"} (fun k => if k.1 = "a" then Attr.ss (NEFinset.of "b" ∅) else Attr.ss (NEFinset.of "c" ∅))) := by
  vector

/-- `map_inside_a_list` -/
theorem map_inside_a_list :
    (denote (Term.array (Term.object (Body.mk ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)) (some (Term.string)))))).e
      (Value.arr [Value.map {"a"} (fun k => Value.str "x")])
    = some (Attr.l [Attr.m {"a"} (fun k => Attr.s "x")]) := by
  vector

/-- `union_of_two` -/
theorem union_of_two :
    (denote (Term.union [Term.string, Term.boolean])).e
      (Value.bool true)
    = some (Attr.bool true) := by
  vector

/-- `nullable_null` -/
theorem nullable_null :
    (denote (Term.union [Term.string, Term.null])).e
      (Value.null)
    = some (Attr.null) := by
  vector

/-- `union_by_literal` -/
theorem union_by_literal :
    (denote (Term.union [Term.object (Body.mk {"kind", "x"} (fun k => if k.1 = "kind" then ObjectSlot.req (Term.literal GroundKind.string "a") else ObjectSlot.req (Term.string)) none), Term.object (Body.mk {"kind", "x"} (fun k => if k.1 = "kind" then ObjectSlot.req (Term.literal GroundKind.string "b") else ObjectSlot.req (Term.boolean)) none)])).e
      (Value.map {"kind", "x"} (fun k => if k.1 = "kind" then Value.str "a" else Value.str "v"))
    = some (Attr.m {"kind", "x"} (fun k => if k.1 = "kind" then Attr.s "a" else Attr.s "v")) := by
  vector

/-- `discriminated_union` -/
theorem discriminated_union :
    (denote (Term.union [Term.object (Body.mk {"kind", "x"} (fun k => if k.1 = "kind" then ObjectSlot.req (Term.literal GroundKind.string "a") else ObjectSlot.req (Term.string)) none), Term.object (Body.mk {"kind", "y"} (fun k => if k.1 = "kind" then ObjectSlot.req (Term.literal GroundKind.string "b") else ObjectSlot.req (Term.boolean)) none)])).e
      (Value.map {"kind", "x"} (fun k => if k.1 = "kind" then Value.str "a" else Value.str "v"))
    = some (Attr.m {"kind", "x"} (fun k => if k.1 = "kind" then Attr.s "a" else Attr.s "v")) := by
  vector

/-- `product_two_objects` -/
theorem product_two_objects :
    (denote (Term.object (Body.mk {"a", "n"} (fun k => if k.1 = "a" then ObjectSlot.req (Term.string) else ObjectSlot.req (Term.boolean)) none))).e
      (Value.map {"a", "n"} (fun k => if k.1 = "a" then Value.str "x" else Value.bool true))
    = some (Attr.m {"a", "n"} (fun k => if k.1 = "a" then Attr.s "x" else Attr.bool true)) := by
  vector

/-- `product_union_object` -/
theorem product_union_object :
    (denote (Term.union [Term.object (Body.mk {"a", "n"} (fun k => if k.1 = "a" then ObjectSlot.req (Term.string) else ObjectSlot.req ((Term.held (Term.number) (Term.string) numeralOfStoredText textOfNumeral))) none), Term.object (Body.mk {"b", "n"} (fun k => if k.1 = "b" then ObjectSlot.req (Term.boolean) else ObjectSlot.req ((Term.held (Term.number) (Term.string) numeralOfStoredText textOfNumeral))) none)])).e
      (Value.map {"a", "n"} (fun k => if k.1 = "a" then Value.str "x" else Value.str "1"))
    = some (Attr.m {"a", "n"} (fun k => if k.1 = "a" then Attr.s "x" else Attr.n (WFNumeral.of "1"))) := by
  vector

/-- `product_three` -/
theorem product_three :
    (denote (Term.object (Body.mk {"p", "q", "r"} (fun k => if k.1 = "p" then ObjectSlot.req (Term.string) else if k.1 = "q" then ObjectSlot.req (Term.boolean) else ObjectSlot.req ((Term.held (Term.number) (Term.string) numeralOfStoredText textOfNumeral))) none))).e
      (Value.map {"p", "q", "r"} (fun k => if k.1 = "p" then Value.str "x" else if k.1 = "q" then Value.bool true else Value.str "1"))
    = some (Attr.m {"p", "q", "r"} (fun k => if k.1 = "p" then Attr.s "x" else if k.1 = "q" then Attr.bool true else Attr.n (WFNumeral.of "1"))) := by
  vector

/-- `dunion_two_keys` -/
theorem dunion_two_keys :
    (denote (Term.union [Term.object (Body.mk {"kind", "size", "toy"} (fun k => if k.1 = "kind" then ObjectSlot.req (Term.literal GroundKind.string "pet") else if k.1 = "size" then ObjectSlot.req (Term.literal GroundKind.string "small") else ObjectSlot.req (Term.string)) none), Term.object (Body.mk {"kind", "size", "pen"} (fun k => if k.1 = "kind" then ObjectSlot.req (Term.literal GroundKind.string "pet") else if k.1 = "size" then ObjectSlot.req (Term.literal GroundKind.string "large") else ObjectSlot.req (Term.string)) none)])).e
      (Value.map {"kind", "size", "toy"} (fun k => if k.1 = "kind" then Value.str "pet" else if k.1 = "size" then Value.str "small" else Value.str "ball"))
    = some (Attr.m {"kind", "size", "toy"} (fun k => if k.1 = "kind" then Attr.s "pet" else if k.1 = "size" then Attr.s "small" else Attr.s "ball")) := by
  vector

/-- `opaque_map` -/
theorem opaque_map :
    (denote (Term.opaq)).e
      (Value.map {"a"} (fun k => Value.str "x"))
    = some (Attr.m {"a"} (fun k => Attr.s "x")) := by
  vector

/-- `lazy_string` -/
theorem lazy_string :
    (denote (Term.string)).e
      (Value.str "x")
    = some (Attr.s "x") := by
  vector

/-- `recursive_json` -/
theorem recursive_json :
    (denote (Term.mu (Term.union [Term.string, Term.array (Term.var 0)]))).e
      (Value.arr [Value.str "a", Value.arr [Value.str "b", Value.arr []]])
    = some (Attr.l [Attr.s "a", Attr.l [Attr.s "b", Attr.l []]]) := by
  vector

/-- `recursive_json__guarded` — the model's guard accepts this term -/
theorem recursive_json__guarded :
    Alg.Term.guarded (Term.mu (Term.union [Term.string, Term.array (Term.var 0)])) = true := rfl

/-- `recursive_tree_optional` -/
theorem recursive_tree_optional :
    (denote (Term.mu (Term.object (Body.mk {"name", "children"} (fun k => if k.1 = "name" then ObjectSlot.req (Term.string) else ObjectSlot.optional (Term.array (Term.var 0))) none)))).e
      (Value.map {"name"} (fun k => Value.str "root"))
    = some (Attr.m {"name"} (fun k => Attr.s "root")) := by
  vector

/-- `recursive_tree_optional__guarded` — the model's guard accepts this term -/
theorem recursive_tree_optional__guarded :
    Alg.Term.guarded (Term.mu (Term.object (Body.mk {"name", "children"} (fun k => if k.1 = "name" then ObjectSlot.req (Term.string) else ObjectSlot.optional (Term.array (Term.var 0))) none))) = true := rfl

/-! ## Refusals — neither side writes anything for these

41 of 1564 shown; `scripts/gate.sh` elaborates all
1564. One `rfl` each, no comparator and no fuel: the answer is `none`,
which carries no function for the funext gap to open under.
-/

/-- `scalar_string__refuses__scalar_boolean` — refused on both sides -/
theorem scalar_string__refuses__scalar_boolean :
    (denote (Term.string)).e
      (Value.bool true) = none := rfl

/-- `scalar_decimal__refuses__scalar_string` — refused on both sides -/
theorem scalar_decimal__refuses__scalar_string :
    (denote ((Term.held (Term.number) (Term.string) numeralOfStoredText textOfNumeral))).e
      (Value.str "hello") = none := rfl

/-- `scalar_boolean__refuses__scalar_string` — refused on both sides -/
theorem scalar_boolean__refuses__scalar_string :
    (denote (Term.boolean)).e
      (Value.str "hello") = none := rfl

/-- `scalar_binary__refuses__scalar_string` — refused on both sides -/
theorem scalar_binary__refuses__scalar_string :
    (denote (Term.binary)).e
      (Value.str "hello") = none := rfl

/-- `scalar_null__refuses__scalar_string` — refused on both sides -/
theorem scalar_null__refuses__scalar_string :
    (denote (Term.null)).e
      (Value.str "hello") = none := rfl

/-- `literal_alternatives__refuses__scalar_string` — refused on both sides -/
theorem literal_alternatives__refuses__scalar_string :
    (denote (Term.union [Term.literal GroundKind.string "A", Term.literal GroundKind.string "B"])).e
      (Value.str "hello") = none := rfl

/-- `literal_decimal__refuses__scalar_string` — refused on both sides -/
theorem literal_decimal__refuses__scalar_string :
    (denote ((Term.held (Term.union [Term.literal GroundKind.number (WFNumeral.of "1"), Term.literal GroundKind.number (WFNumeral.of "2.5")]) (Term.union [Term.literal GroundKind.string "1", Term.literal GroundKind.string "2.5"]) numeralOfStoredText textOfNumeral))).e
      (Value.str "hello") = none := rfl

/-- `literal_non_ascii__refuses__scalar_string` — refused on both sides -/
theorem literal_non_ascii__refuses__scalar_string :
    (denote (Term.union [Term.literal GroundKind.string "⊥", Term.literal GroundKind.string "𝔸"])).e
      (Value.str "hello") = none := rfl

/-- `literal_binary__refuses__scalar_string` — refused on both sides -/
theorem literal_binary__refuses__scalar_string :
    (denote (Term.literal GroundKind.binary [0, 127, 255])).e
      (Value.str "hello") = none := rfl

/-- `set_of_string__refuses__scalar_string` — refused on both sides -/
theorem set_of_string__refuses__scalar_string :
    (denote (Term.set (Term.string))).e
      (Value.str "hello") = none := rfl

/-- `set_of_literal__refuses__scalar_string` — refused on both sides -/
theorem set_of_literal__refuses__scalar_string :
    (denote (Term.set (Term.union [Term.literal GroundKind.string "a", Term.literal GroundKind.string "b"]))).e
      (Value.str "hello") = none := rfl

/-- `set_of_number__refuses__scalar_string` — refused on both sides -/
theorem set_of_number__refuses__scalar_string :
    (denote (Term.set (Term.number))).e
      (Value.str "hello") = none := rfl

/-- `array_of_string__refuses__scalar_string` — refused on both sides -/
theorem array_of_string__refuses__scalar_string :
    (denote (Term.array (Term.string))).e
      (Value.str "hello") = none := rfl

/-- `list_prefix_spread__refuses__scalar_string` — refused on both sides -/
theorem list_prefix_spread__refuses__scalar_string :
    (denote (Term.tuple [Term.string] (some (Term.string)))).e
      (Value.str "hello") = none := rfl

/-- `list_spread_suffix__refuses__scalar_string` — refused on both sides -/
theorem list_spread_suffix__refuses__scalar_string :
    (denote (Term.list [] (some (Term.string)) [Term.boolean])).e
      (Value.str "hello") = none := rfl

/-- `array_empty__refuses__scalar_string` — refused on both sides -/
theorem array_empty__refuses__scalar_string :
    (denote (Term.array (Term.string))).e
      (Value.str "hello") = none := rfl

/-- `tuple_pair__refuses__scalar_string` — refused on both sides -/
theorem tuple_pair__refuses__scalar_string :
    (denote (Term.tuple [Term.string, Term.boolean] none)).e
      (Value.str "hello") = none := rfl

/-- `open_of_string__refuses__scalar_string` — refused on both sides -/
theorem open_of_string__refuses__scalar_string :
    (denote (Term.object (Body.mk ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)) (some (Term.string))))).e
      (Value.str "hello") = none := rfl

/-- `open_empty__refuses__scalar_string` — refused on both sides -/
theorem open_empty__refuses__scalar_string :
    (denote (Term.object (Body.mk ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)) (some (Term.string))))).e
      (Value.str "hello") = none := rfl

/-- `object_two_fields__refuses__scalar_string` — refused on both sides -/
theorem object_two_fields__refuses__scalar_string :
    (denote (Term.object (Body.mk {"a", "b"} (fun k => if k.1 = "a" then ObjectSlot.req (Term.string) else ObjectSlot.req (Term.boolean)) none))).e
      (Value.str "hello") = none := rfl

/-- `object_optional_absent__refuses__scalar_string` — refused on both sides -/
theorem object_optional_absent__refuses__scalar_string :
    (denote (Term.object (Body.mk {"a", "b"} (fun k => if k.1 = "a" then ObjectSlot.req (Term.string) else ObjectSlot.optional (Term.boolean)) none))).e
      (Value.str "hello") = none := rfl

/-- `object_open__refuses__scalar_string` — refused on both sides -/
theorem object_open__refuses__scalar_string :
    (denote (Term.object (Body.mk {"a"} (fun k => ObjectSlot.req (Term.string)) (some (Term.boolean))))).e
      (Value.str "hello") = none := rfl

/-- `object_nested__refuses__scalar_string` — refused on both sides -/
theorem object_nested__refuses__scalar_string :
    (denote (Term.object (Body.mk {"a"} (fun k => ObjectSlot.req (Term.object (Body.mk {"b"} (fun k => ObjectSlot.req (Term.string)) none))) none))).e
      (Value.str "hello") = none := rfl

/-- `open_of_restricted_set__refuses__scalar_string` — refused on both sides -/
theorem open_of_restricted_set__refuses__scalar_string :
    (denote (Term.object (Body.mk ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)) (some (Term.set (Term.union [Term.literal GroundKind.string "a", Term.literal GroundKind.string "b"])))))).e
      (Value.str "hello") = none := rfl

/-- `object_restricted_rest__refuses__scalar_string` — refused on both sides -/
theorem object_restricted_rest__refuses__scalar_string :
    (denote (Term.object (Body.mk {"a"} (fun k => ObjectSlot.req (Term.set (Term.union [Term.literal GroundKind.string "b", Term.literal GroundKind.string "c"]))) (some (Term.set (Term.union [Term.literal GroundKind.string "b", Term.literal GroundKind.string "c"])))))).e
      (Value.str "hello") = none := rfl

/-- `map_inside_a_list__refuses__scalar_string` — refused on both sides -/
theorem map_inside_a_list__refuses__scalar_string :
    (denote (Term.array (Term.object (Body.mk ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)) (some (Term.string)))))).e
      (Value.str "hello") = none := rfl

/-- `union_of_two__refuses__scalar_binary` — refused on both sides -/
theorem union_of_two__refuses__scalar_binary :
    (denote (Term.union [Term.string, Term.boolean])).e
      (Value.bin [0, 127, 255]) = none := rfl

/-- `nullable_null__refuses__scalar_boolean` — refused on both sides -/
theorem nullable_null__refuses__scalar_boolean :
    (denote (Term.union [Term.string, Term.null])).e
      (Value.bool true) = none := rfl

/-- `union_by_literal__refuses__scalar_string` — refused on both sides -/
theorem union_by_literal__refuses__scalar_string :
    (denote (Term.union [Term.object (Body.mk {"kind", "x"} (fun k => if k.1 = "kind" then ObjectSlot.req (Term.literal GroundKind.string "a") else ObjectSlot.req (Term.string)) none), Term.object (Body.mk {"kind", "x"} (fun k => if k.1 = "kind" then ObjectSlot.req (Term.literal GroundKind.string "b") else ObjectSlot.req (Term.boolean)) none)])).e
      (Value.str "hello") = none := rfl

/-- `discriminated_union__refuses__scalar_string` — refused on both sides -/
theorem discriminated_union__refuses__scalar_string :
    (denote (Term.union [Term.object (Body.mk {"kind", "x"} (fun k => if k.1 = "kind" then ObjectSlot.req (Term.literal GroundKind.string "a") else ObjectSlot.req (Term.string)) none), Term.object (Body.mk {"kind", "y"} (fun k => if k.1 = "kind" then ObjectSlot.req (Term.literal GroundKind.string "b") else ObjectSlot.req (Term.boolean)) none)])).e
      (Value.str "hello") = none := rfl

/-- `product_two_objects__refuses__scalar_string` — refused on both sides -/
theorem product_two_objects__refuses__scalar_string :
    (denote (Term.object (Body.mk {"a", "n"} (fun k => if k.1 = "a" then ObjectSlot.req (Term.string) else ObjectSlot.req (Term.boolean)) none))).e
      (Value.str "hello") = none := rfl

/-- `product_union_object__refuses__scalar_string` — refused on both sides -/
theorem product_union_object__refuses__scalar_string :
    (denote (Term.union [Term.object (Body.mk {"a", "n"} (fun k => if k.1 = "a" then ObjectSlot.req (Term.string) else ObjectSlot.req ((Term.held (Term.number) (Term.string) numeralOfStoredText textOfNumeral))) none), Term.object (Body.mk {"b", "n"} (fun k => if k.1 = "b" then ObjectSlot.req (Term.boolean) else ObjectSlot.req ((Term.held (Term.number) (Term.string) numeralOfStoredText textOfNumeral))) none)])).e
      (Value.str "hello") = none := rfl

/-- `product_three__refuses__scalar_string` — refused on both sides -/
theorem product_three__refuses__scalar_string :
    (denote (Term.object (Body.mk {"p", "q", "r"} (fun k => if k.1 = "p" then ObjectSlot.req (Term.string) else if k.1 = "q" then ObjectSlot.req (Term.boolean) else ObjectSlot.req ((Term.held (Term.number) (Term.string) numeralOfStoredText textOfNumeral))) none))).e
      (Value.str "hello") = none := rfl

/-- `dunion_two_keys__refuses__scalar_string` — refused on both sides -/
theorem dunion_two_keys__refuses__scalar_string :
    (denote (Term.union [Term.object (Body.mk {"kind", "size", "toy"} (fun k => if k.1 = "kind" then ObjectSlot.req (Term.literal GroundKind.string "pet") else if k.1 = "size" then ObjectSlot.req (Term.literal GroundKind.string "small") else ObjectSlot.req (Term.string)) none), Term.object (Body.mk {"kind", "size", "pen"} (fun k => if k.1 = "kind" then ObjectSlot.req (Term.literal GroundKind.string "pet") else if k.1 = "size" then ObjectSlot.req (Term.literal GroundKind.string "large") else ObjectSlot.req (Term.string)) none)])).e
      (Value.str "hello") = none := rfl

/-- `lazy_string__refuses__scalar_boolean` — refused on both sides -/
theorem lazy_string__refuses__scalar_boolean :
    (denote (Term.string)).e
      (Value.bool true) = none := rfl

/-- `recursive_json__refuses__scalar_boolean` — refused on both sides -/
theorem recursive_json__refuses__scalar_boolean :
    (denote (Term.mu (Term.union [Term.string, Term.array (Term.var 0)]))).e
      (Value.bool true) = none := rfl

/-- `recursive_tree__refuses__scalar_string` — refused on both sides -/
theorem recursive_tree__refuses__scalar_string :
    (denote (Term.mu (Term.object (Body.mk {"v", "kids"} (fun k => if k.1 = "v" then ObjectSlot.req (Term.string) else ObjectSlot.req (Term.array (Term.var 0))) none)))).e
      (Value.str "hello") = none := rfl

/-- `recursive_category__refuses__scalar_string` — refused on both sides -/
theorem recursive_category__refuses__scalar_string :
    (denote (Term.mu (Term.object (Body.mk {"name", "children"} (fun k => if k.1 = "name" then ObjectSlot.req (Term.string) else ObjectSlot.optional (Term.array (Term.var 0))) none)))).e
      (Value.str "hello") = none := rfl

/-- `recursive_tree_optional__refuses__scalar_string` — refused on both sides -/
theorem recursive_tree_optional__refuses__scalar_string :
    (denote (Term.mu (Term.object (Body.mk {"name", "children"} (fun k => if k.1 = "name" then ObjectSlot.req (Term.string) else ObjectSlot.optional (Term.array (Term.var 0))) none)))).e
      (Value.str "hello") = none := rfl

/-- `scalar_number__refuses__scalar_string` — refused on both sides -/
theorem scalar_number__refuses__scalar_string :
    (denote (Term.number)).e
      (Value.str "hello") = none := rfl

/-- `never__refuses__scalar_string` — refused on both sides -/
theorem never__refuses__scalar_string :
    (denote (Term.never)).e
      (Value.str "hello") = none := rfl

end Calculus
