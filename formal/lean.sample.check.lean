import Calculus.Bridge.Vectors
import Calculus.Dynamo.Lang.Store

/-!
# Differential-testing vectors

**Generated — do not edit.** Emitted by `src/codec/lean.ts` from the shipped TypeScript codecs: each
theorem below is one `encode` this library actually performed, proposed to the model. A failure
here is a disagreement between `src/codec/codec.ts` and `Calculus.denote`, and the theorem's name says
which vector.

The verdict is `Calculus.check`'s, and `check_same` is what makes it worth having: `.same`
*implies* the two attributes are equal, so a line that reduces to `.same` is a proof and not a
comparator's opinion. The fuel on each line is the attribute's own nesting, computed by the
emitter — an under-fuelled line reduces to `.exhausted`, which matches neither `.same` nor
`.differ`, so it fails to compile rather than passing quietly.
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

/-- `scalar_string` -/
theorem scalar_string :
    check 1
      ((denote (libTable noCallers) (Term.string)).e
        (Value.str "hello"))
      (some (Attr.s "hello")) = .same := kernel_rfl%

/-- `scalar_decimal` -/
theorem scalar_decimal :
    check 1
      ((denote (libTable noCallers) ((Term.held false (Term.number) (Term.string) (.decimalText, false) []))).e
        (Value.str "1.5"))
      (some (Attr.n (numeral0))) = .same := kernel_rfl%

/-- `scalar_boolean` -/
theorem scalar_boolean :
    check 1
      ((denote (libTable noCallers) (Term.boolean)).e
        (Value.bool true))
      (some (Attr.bool true)) = .same := kernel_rfl%

/-- `scalar_binary` -/
theorem scalar_binary :
    check 1
      ((denote (libTable noCallers) (Term.binary)).e
        (Value.bin [0, 127, 255]))
      (some (Attr.b [0, 127, 255])) = .same := kernel_rfl%

/-- `scalar_null` -/
theorem scalar_null :
    check 1
      ((denote (libTable noCallers) (Term.null)).e
        (Value.null))
      (some (Attr.null)) = .same := kernel_rfl%

/-- `literal_alternatives` -/
theorem literal_alternatives :
    check 1
      ((denote (libTable noCallers) (Term.union [Term.literal GroundKind.string "A", Term.literal GroundKind.string "B"])).e
        (Value.str "B"))
      (some (Attr.s "B")) = .same := kernel_rfl%

/-- `literal_decimal` -/
theorem literal_decimal :
    check 1
      ((denote (libTable noCallers) ((Term.held false (Term.union [Term.literal GroundKind.number (numeral1), Term.literal GroundKind.number (numeral2)]) (Term.union [Term.literal GroundKind.string "1", Term.literal GroundKind.string "2.5"]) (.decimalText, false) []))).e
        (Value.str "2.5"))
      (some (Attr.n (numeral2))) = .same := kernel_rfl%

/-- `literal_non_ascii` -/
theorem literal_non_ascii :
    check 1
      ((denote (libTable noCallers) (Term.union [Term.literal GroundKind.string "⊥", Term.literal GroundKind.string "𝔸"])).e
        (Value.str "𝔸"))
      (some (Attr.s "𝔸")) = .same := kernel_rfl%

/-- `literal_binary` -/
theorem literal_binary :
    check 1
      ((denote (libTable noCallers) (Term.literal GroundKind.binary [0, 127, 255])).e
        (Value.bin [0, 127, 255]))
      (some (Attr.b [0, 127, 255])) = .same := kernel_rfl%

/-- `set_of_string` -/
theorem set_of_string :
    check 1
      ((denote (libTable noCallers) (Term.set (Term.string))).e
        (Value.strSet (NEFinset.of "b" {"a"})))
      (some (Attr.ss (NEFinset.of "a" {"b"}))) = .same := kernel_rfl%

/-- `set_of_literal` -/
theorem set_of_literal :
    check 1
      ((denote (libTable noCallers) (Term.set (Term.union [Term.literal GroundKind.string "a", Term.literal GroundKind.string "b"]))).e
        (Value.strSet (NEFinset.of "b" {"a"})))
      (some (Attr.ss (NEFinset.of "a" {"b"}))) = .same := kernel_rfl%

/-- `set_of_number` -/
theorem set_of_number :
    check 1
      ((denote (libTable noCallers) (Term.set (Term.number))).e
        (Value.numSet (NEFinset.of (numeral0) {(numeral3)})))
      (some (Attr.ns (NEFinset.of (numeral0) {(numeral3)}))) = .same := kernel_rfl%

/-- `array_of_string` -/
theorem array_of_string :
    check 2
      ((denote (libTable noCallers) (Term.array (Term.string))).e
        (Value.arr [Value.str "a", Value.str "b"]))
      (some (Attr.l [Attr.s "a", Attr.s "b"])) = .same := kernel_rfl%

/-- `list_prefix_spread` -/
theorem list_prefix_spread :
    check 2
      ((denote (libTable noCallers) (Term.tuple [Term.string] (some (Term.string)))).e
        (Value.arr [Value.str "a", Value.str "b", Value.str "c"]))
      (some (Attr.l [Attr.s "a", Attr.s "b", Attr.s "c"])) = .same := kernel_rfl%

/-- `list_spread_suffix` -/
theorem list_spread_suffix :
    check 2
      ((denote (libTable noCallers) (Term.list [] (some (Term.string)) [Term.boolean])).e
        (Value.arr [Value.str "a", Value.str "b", Value.bool true]))
      (some (Attr.l [Attr.s "a", Attr.s "b", Attr.bool true])) = .same := kernel_rfl%

/-- `array_empty` -/
theorem array_empty :
    check 1
      ((denote (libTable noCallers) (Term.array (Term.string))).e
        (Value.arr []))
      (some (Attr.l [])) = .same := kernel_rfl%

/-- `tuple_pair` -/
theorem tuple_pair :
    check 2
      ((denote (libTable noCallers) (Term.tuple [Term.string, Term.boolean] none)).e
        (Value.arr [Value.str "a", Value.bool true]))
      (some (Attr.l [Attr.s "a", Attr.bool true])) = .same := kernel_rfl%

/-- `open_of_string` -/
theorem open_of_string :
    check 2
      ((denote (libTable noCallers) (Term.object (Body.mk ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)) (some (Term.string))))).e
        (Value.map {"a", "b"} (fun k => if k.1 = "a" then Value.str "x" else Value.str "y")))
      (some (Attr.m {"a", "b"} (fun k => if k.1 = "a" then Attr.s "x" else Attr.s "y"))) = .same := kernel_rfl%

/-- `open_empty` -/
theorem open_empty :
    check 1
      ((denote (libTable noCallers) (Term.object (Body.mk ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)) (some (Term.string))))).e
        (Value.map ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1))))
      (some (Attr.m ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)))) = .same := kernel_rfl%

/-- `object_two_fields` -/
theorem object_two_fields :
    check 2
      ((denote (libTable noCallers) (Term.object (Body.mk {"a", "b"} (fun k => if k.1 = "a" then ObjectSlot.req (Term.string) else ObjectSlot.req (Term.boolean)) none))).e
        (Value.map {"a", "b"} (fun k => if k.1 = "a" then Value.str "x" else Value.bool true)))
      (some (Attr.m {"a", "b"} (fun k => if k.1 = "a" then Attr.s "x" else Attr.bool true))) = .same := kernel_rfl%

/-- `object_optional_absent` -/
theorem object_optional_absent :
    check 2
      ((denote (libTable noCallers) (Term.object (Body.mk {"a", "b"} (fun k => if k.1 = "a" then ObjectSlot.req (Term.string) else ObjectSlot.optional (Term.boolean)) none))).e
        (Value.map {"a"} (fun k => Value.str "x")))
      (some (Attr.m {"a"} (fun k => Attr.s "x"))) = .same := kernel_rfl%

/-- `object_fallback_present` -/
theorem object_fallback_present :
    check 2
      ((denote (libTable noCallers) (Term.object (Body.mk {"a"} (fun k => ObjectSlot.fill (Term.string) (Value.str "stand-in")) none))).e
        (Value.map {"a"} (fun k => Value.str "x")))
      (some (Attr.m {"a"} (fun k => Attr.s "x"))) = .same := kernel_rfl%

/-- `object_open` -/
theorem object_open :
    check 2
      ((denote (libTable noCallers) (Term.object (Body.mk {"a"} (fun k => ObjectSlot.req (Term.string)) (some (Term.boolean))))).e
        (Value.map {"a", "z"} (fun k => if k.1 = "a" then Value.str "x" else Value.bool true)))
      (some (Attr.m {"a", "z"} (fun k => if k.1 = "a" then Attr.s "x" else Attr.bool true))) = .same := kernel_rfl%

/-- `object_nested` -/
theorem object_nested :
    check 3
      ((denote (libTable noCallers) (Term.object (Body.mk {"a"} (fun k => ObjectSlot.req (Term.object (Body.mk {"b"} (fun k => ObjectSlot.req (Term.string)) none))) none))).e
        (Value.map {"a"} (fun k => Value.map {"b"} (fun k => Value.str "x"))))
      (some (Attr.m {"a"} (fun k => Attr.m {"b"} (fun k => Attr.s "x")))) = .same := kernel_rfl%

/-- `open_of_restricted_set` -/
theorem open_of_restricted_set :
    check 2
      ((denote (libTable noCallers) (Term.object (Body.mk ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)) (some (Term.set (Term.union [Term.literal GroundKind.string "a", Term.literal GroundKind.string "b"])))))).e
        (Value.map {"a"} (fun k => Value.strSet (NEFinset.of "a" ∅))))
      (some (Attr.m {"a"} (fun k => Attr.ss (NEFinset.of "a" ∅)))) = .same := kernel_rfl%

/-- `object_restricted_rest` -/
theorem object_restricted_rest :
    check 2
      ((denote (libTable noCallers) (Term.object (Body.mk {"a"} (fun k => ObjectSlot.req (Term.set (Term.union [Term.literal GroundKind.string "b", Term.literal GroundKind.string "c"]))) (some (Term.set (Term.union [Term.literal GroundKind.string "b", Term.literal GroundKind.string "c"])))))).e
        (Value.map {"a", "z"} (fun k => if k.1 = "a" then Value.strSet (NEFinset.of "b" ∅) else Value.strSet (NEFinset.of "c" ∅))))
      (some (Attr.m {"a", "z"} (fun k => if k.1 = "a" then Attr.ss (NEFinset.of "b" ∅) else Attr.ss (NEFinset.of "c" ∅)))) = .same := kernel_rfl%

/-- `map_inside_a_list` -/
theorem map_inside_a_list :
    check 3
      ((denote (libTable noCallers) (Term.array (Term.object (Body.mk ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)) (some (Term.string)))))).e
        (Value.arr [Value.map {"a"} (fun k => Value.str "x")]))
      (some (Attr.l [Attr.m {"a"} (fun k => Attr.s "x")])) = .same := kernel_rfl%

/-- `object_with_a_name_inside_a_list` -/
theorem object_with_a_name_inside_a_list :
    check 3
      ((denote (libTable noCallers) (Term.array (Term.object (Body.mk {"a"} (fun k => ObjectSlot.req (Term.string)) none)))).e
        (Value.arr [Value.map {"a"} (fun k => Value.str "x")]))
      (some (Attr.l [Attr.m {"a"} (fun k => Attr.s "x")])) = .same := kernel_rfl%

/-- `open_object_absent_name_inside_a_list` -/
theorem open_object_absent_name_inside_a_list :
    check 3
      ((denote (libTable noCallers) (Term.array (Term.object (Body.mk {"a", "b"} (fun k => if k.1 = "a" then ObjectSlot.req (Term.string) else ObjectSlot.optional (Term.boolean)) (some (Term.boolean)))))).e
        (Value.arr [Value.map {"a", "z"} (fun k => if k.1 = "a" then Value.str "x" else Value.bool true)]))
      (some (Attr.l [Attr.m {"a", "z"} (fun k => if k.1 = "a" then Attr.s "x" else Attr.bool true)])) = .same := kernel_rfl%

/-- `union_of_two` -/
theorem union_of_two :
    check 1
      ((denote (libTable noCallers) (Term.union [Term.string, Term.boolean])).e
        (Value.bool true))
      (some (Attr.bool true)) = .same := kernel_rfl%

/-- `nullable_null` -/
theorem nullable_null :
    check 1
      ((denote (libTable noCallers) (Term.union [Term.string, Term.null])).e
        (Value.null))
      (some (Attr.null)) = .same := kernel_rfl%

/-- `union_by_literal` -/
theorem union_by_literal :
    check 2
      ((denote (libTable noCallers) (Term.union [Term.object (Body.mk {"kind", "x"} (fun k => if k.1 = "kind" then ObjectSlot.req (Term.literal GroundKind.string "a") else ObjectSlot.req (Term.string)) none), Term.object (Body.mk {"kind", "x"} (fun k => if k.1 = "kind" then ObjectSlot.req (Term.literal GroundKind.string "b") else ObjectSlot.req (Term.boolean)) none)])).e
        (Value.map {"kind", "x"} (fun k => if k.1 = "kind" then Value.str "a" else Value.str "v")))
      (some (Attr.m {"kind", "x"} (fun k => if k.1 = "kind" then Attr.s "a" else Attr.s "v"))) = .same := kernel_rfl%

/-- `discriminated_union` -/
theorem discriminated_union :
    check 2
      ((denote (libTable noCallers) (Term.union [Term.object (Body.mk {"kind", "x"} (fun k => if k.1 = "kind" then ObjectSlot.req (Term.literal GroundKind.string "a") else ObjectSlot.req (Term.string)) none), Term.object (Body.mk {"kind", "y"} (fun k => if k.1 = "kind" then ObjectSlot.req (Term.literal GroundKind.string "b") else ObjectSlot.req (Term.boolean)) none)])).e
        (Value.map {"kind", "x"} (fun k => if k.1 = "kind" then Value.str "a" else Value.str "v")))
      (some (Attr.m {"kind", "x"} (fun k => if k.1 = "kind" then Attr.s "a" else Attr.s "v"))) = .same := kernel_rfl%

/-- `product_two_objects` -/
theorem product_two_objects :
    check 2
      ((denote (libTable noCallers) (Term.object (Body.mk {"a", "n"} (fun k => if k.1 = "a" then ObjectSlot.req (Term.string) else ObjectSlot.req (Term.boolean)) none))).e
        (Value.map {"a", "n"} (fun k => if k.1 = "a" then Value.str "x" else Value.bool true)))
      (some (Attr.m {"a", "n"} (fun k => if k.1 = "a" then Attr.s "x" else Attr.bool true))) = .same := kernel_rfl%

/-- `product_union_object` -/
theorem product_union_object :
    check 2
      ((denote (libTable noCallers) (Term.union [Term.object (Body.mk {"a", "n"} (fun k => if k.1 = "a" then ObjectSlot.req (Term.string) else ObjectSlot.req ((Term.held false (Term.number) (Term.string) (.decimalText, false) []))) none), Term.object (Body.mk {"b", "n"} (fun k => if k.1 = "b" then ObjectSlot.req (Term.boolean) else ObjectSlot.req ((Term.held false (Term.number) (Term.string) (.decimalText, false) []))) none)])).e
        (Value.map {"a", "n"} (fun k => if k.1 = "a" then Value.str "x" else Value.str "1")))
      (some (Attr.m {"a", "n"} (fun k => if k.1 = "a" then Attr.s "x" else Attr.n (numeral1)))) = .same := kernel_rfl%

/-- `product_three` -/
theorem product_three :
    check 2
      ((denote (libTable noCallers) (Term.object (Body.mk {"p", "q", "r"} (fun k => if k.1 = "p" then ObjectSlot.req (Term.string) else if k.1 = "q" then ObjectSlot.req (Term.boolean) else ObjectSlot.req ((Term.held false (Term.number) (Term.string) (.decimalText, false) []))) none))).e
        (Value.map {"p", "q", "r"} (fun k => if k.1 = "p" then Value.str "x" else if k.1 = "q" then Value.bool true else Value.str "1")))
      (some (Attr.m {"p", "q", "r"} (fun k => if k.1 = "p" then Attr.s "x" else if k.1 = "q" then Attr.bool true else Attr.n (numeral1)))) = .same := kernel_rfl%

/-- `dunion_two_keys` -/
theorem dunion_two_keys :
    check 2
      ((denote (libTable noCallers) (Term.union [Term.object (Body.mk {"kind", "size", "toy"} (fun k => if k.1 = "kind" then ObjectSlot.req (Term.literal GroundKind.string "pet") else if k.1 = "size" then ObjectSlot.req (Term.literal GroundKind.string "small") else ObjectSlot.req (Term.string)) none), Term.object (Body.mk {"kind", "size", "pen"} (fun k => if k.1 = "kind" then ObjectSlot.req (Term.literal GroundKind.string "pet") else if k.1 = "size" then ObjectSlot.req (Term.literal GroundKind.string "large") else ObjectSlot.req (Term.string)) none)])).e
        (Value.map {"kind", "size", "toy"} (fun k => if k.1 = "kind" then Value.str "pet" else if k.1 = "size" then Value.str "small" else Value.str "ball")))
      (some (Attr.m {"kind", "size", "toy"} (fun k => if k.1 = "kind" then Attr.s "pet" else if k.1 = "size" then Attr.s "small" else Attr.s "ball"))) = .same := kernel_rfl%

/-- `opaque_map` -/
theorem opaque_map :
    check 2
      ((denote (libTable noCallers) (Term.opaq)).e
        (Value.map {"a"} (fun k => Value.str "x")))
      (some (Attr.m {"a"} (fun k => Attr.s "x"))) = .same := kernel_rfl%

/-- `lazy_string` -/
theorem lazy_string :
    check 1
      ((denote (libTable noCallers) (Term.string)).e
        (Value.str "x"))
      (some (Attr.s "x")) = .same := kernel_rfl%

/-- `recursive_json` -/
theorem recursive_json :
    check 3
      ((denote (libTable noCallers) (Term.mu (Term.union [Term.string, Term.array (Term.var 0)]))).e
        (Value.arr [Value.str "a", Value.arr [Value.str "b", Value.arr []]]))
      (some (Attr.l [Attr.s "a", Attr.l [Attr.s "b", Attr.l []]])) = .same := kernel_rfl%

/-- `recursive_json__guarded` — the model's guard accepts this term -/
theorem recursive_json__guarded :
    Alg.Term.guarded (Term.mu (Term.union [Term.string, Term.array (Term.var 0)])) = true := kernel_rfl%

/-- `recursive_tree` -/
theorem recursive_tree :
    check 4
      ((denote (libTable noCallers) (Term.mu (Term.object (Body.mk {"v", "kids"} (fun k => if k.1 = "v" then ObjectSlot.req (Term.string) else ObjectSlot.req (Term.array (Term.var 0))) none)))).e
        (Value.map {"v", "kids"} (fun k => if k.1 = "v" then Value.str "r" else Value.arr [Value.map {"v", "kids"} (fun k => if k.1 = "v" then Value.str "c" else Value.arr [])])))
      (some (Attr.m {"v", "kids"} (fun k => if k.1 = "v" then Attr.s "r" else Attr.l [Attr.m {"v", "kids"} (fun k => if k.1 = "v" then Attr.s "c" else Attr.l [])]))) = .same := kernel_rfl%

/-- `recursive_tree__guarded` — the model's guard accepts this term -/
theorem recursive_tree__guarded :
    Alg.Term.guarded (Term.mu (Term.object (Body.mk {"v", "kids"} (fun k => if k.1 = "v" then ObjectSlot.req (Term.string) else ObjectSlot.req (Term.array (Term.var 0))) none))) = true := kernel_rfl%

/-- `recursive_category` -/
theorem recursive_category :
    check 4
      ((denote (libTable noCallers) (Term.mu (Term.object (Body.mk {"name", "children"} (fun k => if k.1 = "name" then ObjectSlot.req (Term.string) else ObjectSlot.optional (Term.array (Term.var 0))) none)))).e
        (Value.map {"name", "children"} (fun k => if k.1 = "name" then Value.str "pets" else Value.arr [Value.map {"name"} (fun k => Value.str "dogs")])))
      (some (Attr.m {"name", "children"} (fun k => if k.1 = "name" then Attr.s "pets" else Attr.l [Attr.m {"name"} (fun k => Attr.s "dogs")]))) = .same := kernel_rfl%

/-- `recursive_category__guarded` — the model's guard accepts this term -/
theorem recursive_category__guarded :
    Alg.Term.guarded (Term.mu (Term.object (Body.mk {"name", "children"} (fun k => if k.1 = "name" then ObjectSlot.req (Term.string) else ObjectSlot.optional (Term.array (Term.var 0))) none))) = true := kernel_rfl%

/-- `recursive_tree_optional` -/
theorem recursive_tree_optional :
    check 2
      ((denote (libTable noCallers) (Term.mu (Term.object (Body.mk {"name", "children"} (fun k => if k.1 = "name" then ObjectSlot.req (Term.string) else ObjectSlot.optional (Term.array (Term.var 0))) none)))).e
        (Value.map {"name"} (fun k => Value.str "root")))
      (some (Attr.m {"name"} (fun k => Attr.s "root"))) = .same := kernel_rfl%

/-- `recursive_tree_optional__guarded` — the model's guard accepts this term -/
theorem recursive_tree_optional__guarded :
    Alg.Term.guarded (Term.mu (Term.object (Body.mk {"name", "children"} (fun k => if k.1 = "name" then ObjectSlot.req (Term.string) else ObjectSlot.optional (Term.array (Term.var 0))) none))) = true := kernel_rfl%

/-! ### Read back, through the same term

The model's `p`, given the attribute the library wrote, against the value the library read. Only
the `check` sample carries these: a read vector's answer is a `Value`, so it needs `vcheck`, and
the `equation` sample states each vector as an equation on `denote` by design. -/

/-- `scalar_string` — read back through the term that wrote it -/
theorem scalar_string__reads :
    vcheck 1
      ((denote (libTable noCallers) (Term.string)).p
        (Attr.s "hello"))
      (some (Value.str "hello")) = .same := kernel_rfl%

/-- `scalar_boolean` — read back through the term that wrote it -/
theorem scalar_boolean__reads :
    vcheck 1
      ((denote (libTable noCallers) (Term.boolean)).p
        (Attr.bool true))
      (some (Value.bool true)) = .same := kernel_rfl%

/-- `set_of_string` — read back through the term that wrote it -/
theorem set_of_string__reads :
    vcheck 1
      ((denote (libTable noCallers) (Term.set (Term.string))).p
        (Attr.ss (NEFinset.of "a" {"b"})))
      (some (Value.strSet (NEFinset.of "a" {"b"}))) = .same := kernel_rfl%

/-- `array_of_string` — read back through the term that wrote it -/
theorem array_of_string__reads :
    vcheck 2
      ((denote (libTable noCallers) (Term.array (Term.string))).p
        (Attr.l [Attr.s "a", Attr.s "b"]))
      (some (Value.arr [Value.str "a", Value.str "b"])) = .same := kernel_rfl%

/-- `object_two_fields` — read back through the term that wrote it -/
theorem object_two_fields__reads :
    vcheck 2
      ((denote (libTable noCallers) (Term.object (Body.mk {"a", "b"} (fun k => if k.1 = "a" then ObjectSlot.req (Term.string) else ObjectSlot.req (Term.boolean)) none))).p
        (Attr.m {"a", "b"} (fun k => if k.1 = "a" then Attr.s "x" else Attr.bool true)))
      (some (Value.map {"a", "b"} (fun k => if k.1 = "a" then Value.str "x" else Value.bool true))) = .same := kernel_rfl%

/-- `union_of_two` — read back through the term that wrote it -/
theorem union_of_two__reads :
    vcheck 1
      ((denote (libTable noCallers) (Term.union [Term.string, Term.boolean])).p
        (Attr.bool true))
      (some (Value.bool true)) = .same := kernel_rfl%

/-! ## Refusals — neither side writes anything for these

44 of 1764 shown; `scripts/gate.sh` elaborates all
1764. One `kernel_rfl%` each, no comparator and no fuel: the answer is `none`,
which carries no function for the funext gap to open under.
-/

/-- `scalar_string__refuses__scalar_boolean` — refused on both sides -/
theorem scalar_string__refuses__scalar_boolean :
    (denote (libTable noCallers) (Term.string)).e
      (Value.bool true) = none := kernel_rfl%

/-- `scalar_decimal__refuses__scalar_string` — refused on both sides -/
theorem scalar_decimal__refuses__scalar_string :
    (denote (libTable noCallers) ((Term.held false (Term.number) (Term.string) (.decimalText, false) []))).e
      (Value.str "hello") = none := kernel_rfl%

/-- `scalar_boolean__refuses__scalar_string` — refused on both sides -/
theorem scalar_boolean__refuses__scalar_string :
    (denote (libTable noCallers) (Term.boolean)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `scalar_binary__refuses__scalar_string` — refused on both sides -/
theorem scalar_binary__refuses__scalar_string :
    (denote (libTable noCallers) (Term.binary)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `scalar_null__refuses__scalar_string` — refused on both sides -/
theorem scalar_null__refuses__scalar_string :
    (denote (libTable noCallers) (Term.null)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `literal_alternatives__refuses__scalar_string` — refused on both sides -/
theorem literal_alternatives__refuses__scalar_string :
    (denote (libTable noCallers) (Term.union [Term.literal GroundKind.string "A", Term.literal GroundKind.string "B"])).e
      (Value.str "hello") = none := kernel_rfl%

/-- `literal_decimal__refuses__scalar_string` — refused on both sides -/
theorem literal_decimal__refuses__scalar_string :
    (denote (libTable noCallers) ((Term.held false (Term.union [Term.literal GroundKind.number (numeral1), Term.literal GroundKind.number (numeral2)]) (Term.union [Term.literal GroundKind.string "1", Term.literal GroundKind.string "2.5"]) (.decimalText, false) []))).e
      (Value.str "hello") = none := kernel_rfl%

/-- `literal_non_ascii__refuses__scalar_string` — refused on both sides -/
theorem literal_non_ascii__refuses__scalar_string :
    (denote (libTable noCallers) (Term.union [Term.literal GroundKind.string "⊥", Term.literal GroundKind.string "𝔸"])).e
      (Value.str "hello") = none := kernel_rfl%

/-- `literal_binary__refuses__scalar_string` — refused on both sides -/
theorem literal_binary__refuses__scalar_string :
    (denote (libTable noCallers) (Term.literal GroundKind.binary [0, 127, 255])).e
      (Value.str "hello") = none := kernel_rfl%

/-- `set_of_string__refuses__scalar_string` — refused on both sides -/
theorem set_of_string__refuses__scalar_string :
    (denote (libTable noCallers) (Term.set (Term.string))).e
      (Value.str "hello") = none := kernel_rfl%

/-- `set_of_literal__refuses__scalar_string` — refused on both sides -/
theorem set_of_literal__refuses__scalar_string :
    (denote (libTable noCallers) (Term.set (Term.union [Term.literal GroundKind.string "a", Term.literal GroundKind.string "b"]))).e
      (Value.str "hello") = none := kernel_rfl%

/-- `set_of_number__refuses__scalar_string` — refused on both sides -/
theorem set_of_number__refuses__scalar_string :
    (denote (libTable noCallers) (Term.set (Term.number))).e
      (Value.str "hello") = none := kernel_rfl%

/-- `array_of_string__refuses__scalar_string` — refused on both sides -/
theorem array_of_string__refuses__scalar_string :
    (denote (libTable noCallers) (Term.array (Term.string))).e
      (Value.str "hello") = none := kernel_rfl%

/-- `list_prefix_spread__refuses__scalar_string` — refused on both sides -/
theorem list_prefix_spread__refuses__scalar_string :
    (denote (libTable noCallers) (Term.tuple [Term.string] (some (Term.string)))).e
      (Value.str "hello") = none := kernel_rfl%

/-- `list_spread_suffix__refuses__scalar_string` — refused on both sides -/
theorem list_spread_suffix__refuses__scalar_string :
    (denote (libTable noCallers) (Term.list [] (some (Term.string)) [Term.boolean])).e
      (Value.str "hello") = none := kernel_rfl%

/-- `array_empty__refuses__scalar_string` — refused on both sides -/
theorem array_empty__refuses__scalar_string :
    (denote (libTable noCallers) (Term.array (Term.string))).e
      (Value.str "hello") = none := kernel_rfl%

/-- `tuple_pair__refuses__scalar_string` — refused on both sides -/
theorem tuple_pair__refuses__scalar_string :
    (denote (libTable noCallers) (Term.tuple [Term.string, Term.boolean] none)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `open_of_string__refuses__scalar_string` — refused on both sides -/
theorem open_of_string__refuses__scalar_string :
    (denote (libTable noCallers) (Term.object (Body.mk ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)) (some (Term.string))))).e
      (Value.str "hello") = none := kernel_rfl%

/-- `open_empty__refuses__scalar_string` — refused on both sides -/
theorem open_empty__refuses__scalar_string :
    (denote (libTable noCallers) (Term.object (Body.mk ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)) (some (Term.string))))).e
      (Value.str "hello") = none := kernel_rfl%

/-- `object_two_fields__refuses__scalar_string` — refused on both sides -/
theorem object_two_fields__refuses__scalar_string :
    (denote (libTable noCallers) (Term.object (Body.mk {"a", "b"} (fun k => if k.1 = "a" then ObjectSlot.req (Term.string) else ObjectSlot.req (Term.boolean)) none))).e
      (Value.str "hello") = none := kernel_rfl%

/-- `object_optional_absent__refuses__scalar_string` — refused on both sides -/
theorem object_optional_absent__refuses__scalar_string :
    (denote (libTable noCallers) (Term.object (Body.mk {"a", "b"} (fun k => if k.1 = "a" then ObjectSlot.req (Term.string) else ObjectSlot.optional (Term.boolean)) none))).e
      (Value.str "hello") = none := kernel_rfl%

/-- `object_fallback_present__refuses__scalar_string` — refused on both sides -/
theorem object_fallback_present__refuses__scalar_string :
    (denote (libTable noCallers) (Term.object (Body.mk {"a"} (fun k => ObjectSlot.fill (Term.string) (Value.str "stand-in")) none))).e
      (Value.str "hello") = none := kernel_rfl%

/-- `object_open__refuses__scalar_string` — refused on both sides -/
theorem object_open__refuses__scalar_string :
    (denote (libTable noCallers) (Term.object (Body.mk {"a"} (fun k => ObjectSlot.req (Term.string)) (some (Term.boolean))))).e
      (Value.str "hello") = none := kernel_rfl%

/-- `object_nested__refuses__scalar_string` — refused on both sides -/
theorem object_nested__refuses__scalar_string :
    (denote (libTable noCallers) (Term.object (Body.mk {"a"} (fun k => ObjectSlot.req (Term.object (Body.mk {"b"} (fun k => ObjectSlot.req (Term.string)) none))) none))).e
      (Value.str "hello") = none := kernel_rfl%

/-- `open_of_restricted_set__refuses__scalar_string` — refused on both sides -/
theorem open_of_restricted_set__refuses__scalar_string :
    (denote (libTable noCallers) (Term.object (Body.mk ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)) (some (Term.set (Term.union [Term.literal GroundKind.string "a", Term.literal GroundKind.string "b"])))))).e
      (Value.str "hello") = none := kernel_rfl%

/-- `object_restricted_rest__refuses__scalar_string` — refused on both sides -/
theorem object_restricted_rest__refuses__scalar_string :
    (denote (libTable noCallers) (Term.object (Body.mk {"a"} (fun k => ObjectSlot.req (Term.set (Term.union [Term.literal GroundKind.string "b", Term.literal GroundKind.string "c"]))) (some (Term.set (Term.union [Term.literal GroundKind.string "b", Term.literal GroundKind.string "c"])))))).e
      (Value.str "hello") = none := kernel_rfl%

/-- `map_inside_a_list__refuses__scalar_string` — refused on both sides -/
theorem map_inside_a_list__refuses__scalar_string :
    (denote (libTable noCallers) (Term.array (Term.object (Body.mk ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)) (some (Term.string)))))).e
      (Value.str "hello") = none := kernel_rfl%

/-- `object_with_a_name_inside_a_list__refuses__scalar_string` — refused on both sides -/
theorem object_with_a_name_inside_a_list__refuses__scalar_string :
    (denote (libTable noCallers) (Term.array (Term.object (Body.mk {"a"} (fun k => ObjectSlot.req (Term.string)) none)))).e
      (Value.str "hello") = none := kernel_rfl%

/-- `open_object_absent_name_inside_a_list__refuses__scalar_string` — refused on both sides -/
theorem open_object_absent_name_inside_a_list__refuses__scalar_string :
    (denote (libTable noCallers) (Term.array (Term.object (Body.mk {"a", "b"} (fun k => if k.1 = "a" then ObjectSlot.req (Term.string) else ObjectSlot.optional (Term.boolean)) (some (Term.boolean)))))).e
      (Value.str "hello") = none := kernel_rfl%

/-- `union_of_two__refuses__scalar_binary` — refused on both sides -/
theorem union_of_two__refuses__scalar_binary :
    (denote (libTable noCallers) (Term.union [Term.string, Term.boolean])).e
      (Value.bin [0, 127, 255]) = none := kernel_rfl%

/-- `nullable_null__refuses__scalar_boolean` — refused on both sides -/
theorem nullable_null__refuses__scalar_boolean :
    (denote (libTable noCallers) (Term.union [Term.string, Term.null])).e
      (Value.bool true) = none := kernel_rfl%

/-- `union_by_literal__refuses__scalar_string` — refused on both sides -/
theorem union_by_literal__refuses__scalar_string :
    (denote (libTable noCallers) (Term.union [Term.object (Body.mk {"kind", "x"} (fun k => if k.1 = "kind" then ObjectSlot.req (Term.literal GroundKind.string "a") else ObjectSlot.req (Term.string)) none), Term.object (Body.mk {"kind", "x"} (fun k => if k.1 = "kind" then ObjectSlot.req (Term.literal GroundKind.string "b") else ObjectSlot.req (Term.boolean)) none)])).e
      (Value.str "hello") = none := kernel_rfl%

/-- `discriminated_union__refuses__scalar_string` — refused on both sides -/
theorem discriminated_union__refuses__scalar_string :
    (denote (libTable noCallers) (Term.union [Term.object (Body.mk {"kind", "x"} (fun k => if k.1 = "kind" then ObjectSlot.req (Term.literal GroundKind.string "a") else ObjectSlot.req (Term.string)) none), Term.object (Body.mk {"kind", "y"} (fun k => if k.1 = "kind" then ObjectSlot.req (Term.literal GroundKind.string "b") else ObjectSlot.req (Term.boolean)) none)])).e
      (Value.str "hello") = none := kernel_rfl%

/-- `product_two_objects__refuses__scalar_string` — refused on both sides -/
theorem product_two_objects__refuses__scalar_string :
    (denote (libTable noCallers) (Term.object (Body.mk {"a", "n"} (fun k => if k.1 = "a" then ObjectSlot.req (Term.string) else ObjectSlot.req (Term.boolean)) none))).e
      (Value.str "hello") = none := kernel_rfl%

/-- `product_union_object__refuses__scalar_string` — refused on both sides -/
theorem product_union_object__refuses__scalar_string :
    (denote (libTable noCallers) (Term.union [Term.object (Body.mk {"a", "n"} (fun k => if k.1 = "a" then ObjectSlot.req (Term.string) else ObjectSlot.req ((Term.held false (Term.number) (Term.string) (.decimalText, false) []))) none), Term.object (Body.mk {"b", "n"} (fun k => if k.1 = "b" then ObjectSlot.req (Term.boolean) else ObjectSlot.req ((Term.held false (Term.number) (Term.string) (.decimalText, false) []))) none)])).e
      (Value.str "hello") = none := kernel_rfl%

/-- `product_three__refuses__scalar_string` — refused on both sides -/
theorem product_three__refuses__scalar_string :
    (denote (libTable noCallers) (Term.object (Body.mk {"p", "q", "r"} (fun k => if k.1 = "p" then ObjectSlot.req (Term.string) else if k.1 = "q" then ObjectSlot.req (Term.boolean) else ObjectSlot.req ((Term.held false (Term.number) (Term.string) (.decimalText, false) []))) none))).e
      (Value.str "hello") = none := kernel_rfl%

/-- `dunion_two_keys__refuses__scalar_string` — refused on both sides -/
theorem dunion_two_keys__refuses__scalar_string :
    (denote (libTable noCallers) (Term.union [Term.object (Body.mk {"kind", "size", "toy"} (fun k => if k.1 = "kind" then ObjectSlot.req (Term.literal GroundKind.string "pet") else if k.1 = "size" then ObjectSlot.req (Term.literal GroundKind.string "small") else ObjectSlot.req (Term.string)) none), Term.object (Body.mk {"kind", "size", "pen"} (fun k => if k.1 = "kind" then ObjectSlot.req (Term.literal GroundKind.string "pet") else if k.1 = "size" then ObjectSlot.req (Term.literal GroundKind.string "large") else ObjectSlot.req (Term.string)) none)])).e
      (Value.str "hello") = none := kernel_rfl%

/-- `lazy_string__refuses__scalar_boolean` — refused on both sides -/
theorem lazy_string__refuses__scalar_boolean :
    (denote (libTable noCallers) (Term.string)).e
      (Value.bool true) = none := kernel_rfl%

/-- `recursive_json__refuses__scalar_boolean` — refused on both sides -/
theorem recursive_json__refuses__scalar_boolean :
    (denote (libTable noCallers) (Term.mu (Term.union [Term.string, Term.array (Term.var 0)]))).e
      (Value.bool true) = none := kernel_rfl%

/-- `recursive_tree__refuses__scalar_string` — refused on both sides -/
theorem recursive_tree__refuses__scalar_string :
    (denote (libTable noCallers) (Term.mu (Term.object (Body.mk {"v", "kids"} (fun k => if k.1 = "v" then ObjectSlot.req (Term.string) else ObjectSlot.req (Term.array (Term.var 0))) none)))).e
      (Value.str "hello") = none := kernel_rfl%

/-- `recursive_category__refuses__scalar_string` — refused on both sides -/
theorem recursive_category__refuses__scalar_string :
    (denote (libTable noCallers) (Term.mu (Term.object (Body.mk {"name", "children"} (fun k => if k.1 = "name" then ObjectSlot.req (Term.string) else ObjectSlot.optional (Term.array (Term.var 0))) none)))).e
      (Value.str "hello") = none := kernel_rfl%

/-- `recursive_tree_optional__refuses__scalar_string` — refused on both sides -/
theorem recursive_tree_optional__refuses__scalar_string :
    (denote (libTable noCallers) (Term.mu (Term.object (Body.mk {"name", "children"} (fun k => if k.1 = "name" then ObjectSlot.req (Term.string) else ObjectSlot.optional (Term.array (Term.var 0))) none)))).e
      (Value.str "hello") = none := kernel_rfl%

/-- `scalar_number__refuses__scalar_string` — refused on both sides -/
theorem scalar_number__refuses__scalar_string :
    (denote (libTable noCallers) (Term.number)).e
      (Value.str "hello") = none := kernel_rfl%

/-- `never__refuses__scalar_string` — refused on both sides -/
theorem never__refuses__scalar_string :
    (denote (libTable noCallers) (Term.never)).e
      (Value.str "hello") = none := kernel_rfl%

end Calculus
