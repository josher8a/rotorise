import Calculus.Vectors
import Calculus.Separation

/-!
# Differential-testing vectors

**Generated — do not edit.** Emitted by `src/codec/lean.ts` from the shipped TypeScript codecs: each
theorem below is one `encode` this library actually performed, proposed to the model. A failure
here is a disagreement between `src/codec/codec.ts` and `Calculus.denote`, and the theorem's name says
which vector.

The verdict is `Calculus.check`'s, and `check_same` is what makes it worth having: `.same`
*implies* the two attributes are equal, so a line that reduces to `.same` is a proof and not a
comparator's opinion. The fuel on each line is the attribute's own nesting, computed by the
generator — an under-fuelled line reduces to `.exhausted`, which matches neither `.same` nor
`.differ`, so it fails to compile rather than passing quietly.
-/

/-! A key function is emitted total on the membership subtype, so a single-declared-name object
binds a `k` it never reads. `Calculus/` itself builds warning-free and so should this file; the
binder cannot be `_` because a multi-name object *does* read `k.1`. -/
set_option linter.unusedVariables false
/-! A vector's name spells the codec pair it came from, so it carries `__`. -/
set_option linter.style.nameCheck false

namespace Calculus

/-- `scalar_string` -/
theorem scalar_string :
    check 1
      ((denote (Term.string)).e
        (Value.str "hello"))
      (some (Attr.s "hello")) = .same := rfl

/-- `scalar_decimal` -/
theorem scalar_decimal :
    check 1
      ((denote ((Term.held (Term.number) numeralOfStoredText textOfNumeral))).e
        (Value.str "1.5"))
      (some (Attr.n (WFNumeral.of "1.5"))) = .same := rfl

/-- `scalar_boolean` -/
theorem scalar_boolean :
    check 1
      ((denote (Term.boolean)).e
        (Value.bool true))
      (some (Attr.bool true)) = .same := rfl

/-- `scalar_binary` -/
theorem scalar_binary :
    check 1
      ((denote (Term.binary)).e
        (Value.bin [0, 127, 255]))
      (some (Attr.b [0, 127, 255])) = .same := rfl

/-- `scalar_null` -/
theorem scalar_null :
    check 1
      ((denote (Term.null)).e
        (Value.null))
      (some (Attr.null)) = .same := rfl

/-- `literal_alternatives` -/
theorem literal_alternatives :
    check 1
      ((denote (Term.union [Term.literal GroundKind.string "A", Term.literal GroundKind.string "B"])).e
        (Value.str "B"))
      (some (Attr.s "B")) = .same := rfl

/-- `literal_decimal` -/
theorem literal_decimal :
    check 1
      ((denote ((Term.held (Term.union [Term.literal GroundKind.number (WFNumeral.of "1"), Term.literal GroundKind.number (WFNumeral.of "2.5")]) numeralOfStoredText textOfNumeral))).e
        (Value.str "2.5"))
      (some (Attr.n (WFNumeral.of "2.5"))) = .same := rfl

/-- `literal_non_ascii` -/
theorem literal_non_ascii :
    check 1
      ((denote (Term.union [Term.literal GroundKind.string "⊥", Term.literal GroundKind.string "𝔸"])).e
        (Value.str "𝔸"))
      (some (Attr.s "𝔸")) = .same := rfl

/-- `literal_binary` -/
theorem literal_binary :
    check 1
      ((denote (Term.literal GroundKind.binary [0, 127, 255])).e
        (Value.bin [0, 127, 255]))
      (some (Attr.b [0, 127, 255])) = .same := rfl

/-- `set_of_string` -/
theorem set_of_string :
    check 1
      ((denote (Term.set SetBase.string)).e
        (Value.strSet (NEFinset.of "b" {"a"})))
      (some (Attr.ss (NEFinset.of "a" {"b"}))) = .same := rfl

/-- `set_of_literal` -/
theorem set_of_literal :
    check 1
      ((denote (Term.refine (Term.set SetBase.string) (Pred.each (Pred.members GroundKind.string (NEFinset.of "a" {"b"}))))).e
        (Value.strSet (NEFinset.of "b" {"a"})))
      (some (Attr.ss (NEFinset.of "a" {"b"}))) = .same := rfl

/-- `set_of_number` -/
theorem set_of_number :
    check 1
      ((denote (Term.set SetBase.number)).e
        (Value.numSet (NEFinset.of (WFNumeral.of "1.5") {(WFNumeral.of "2")})))
      (some (Attr.ns (NEFinset.of (WFNumeral.of "1.5") {(WFNumeral.of "2")}))) = .same := rfl

/-- `array_of_string` -/
theorem array_of_string :
    check 2
      ((denote (Term.array (Term.string))).e
        (Value.arr [Value.str "a", Value.str "b"]))
      (some (Attr.l [Attr.s "a", Attr.s "b"])) = .same := rfl

/-- `list_prefix_spread` -/
theorem list_prefix_spread :
    check 2
      ((denote (Term.tuple [Term.string] (some (Term.string)))).e
        (Value.arr [Value.str "a", Value.str "b", Value.str "c"]))
      (some (Attr.l [Attr.s "a", Attr.s "b", Attr.s "c"])) = .same := rfl

/-- `list_spread_suffix` -/
theorem list_spread_suffix :
    check 2
      ((denote (Term.list [] (some (Term.string)) [Term.boolean])).e
        (Value.arr [Value.str "a", Value.str "b", Value.bool true]))
      (some (Attr.l [Attr.s "a", Attr.s "b", Attr.bool true])) = .same := rfl

/-- `array_empty` -/
theorem array_empty :
    check 1
      ((denote (Term.array (Term.string))).e
        (Value.arr []))
      (some (Attr.l [])) = .same := rfl

/-- `tuple_pair` -/
theorem tuple_pair :
    check 2
      ((denote (Term.tuple [Term.string, Term.boolean] none)).e
        (Value.arr [Value.str "a", Value.bool true]))
      (some (Attr.l [Attr.s "a", Attr.bool true])) = .same := rfl

/-- `open_of_string` -/
theorem open_of_string :
    check 2
      ((denote (Term.object (Body.mk ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)) (some (Term.string))))).e
        (Value.map {"a", "b"} (fun k => if k.1 = "a" then Value.str "x" else Value.str "y")))
      (some (Attr.m {"a", "b"} (fun k => if k.1 = "a" then Attr.s "x" else Attr.s "y"))) = .same := rfl

/-- `open_empty` -/
theorem open_empty :
    check 1
      ((denote (Term.object (Body.mk ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)) (some (Term.string))))).e
        (Value.map ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1))))
      (some (Attr.m ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)))) = .same := rfl

/-- `object_two_fields` -/
theorem object_two_fields :
    check 2
      ((denote (Term.object (Body.mk {"a", "b"} (fun k => if k.1 = "a" then ObjectSlot.req (Term.string) else ObjectSlot.req (Term.boolean)) none))).e
        (Value.map {"a", "b"} (fun k => if k.1 = "a" then Value.str "x" else Value.bool true)))
      (some (Attr.m {"a", "b"} (fun k => if k.1 = "a" then Attr.s "x" else Attr.bool true))) = .same := rfl

/-- `object_optional_absent` -/
theorem object_optional_absent :
    check 2
      ((denote (Term.object (Body.mk {"a", "b"} (fun k => if k.1 = "a" then ObjectSlot.req (Term.string) else ObjectSlot.optional (Term.boolean)) none))).e
        (Value.map {"a"} (fun k => Value.str "x")))
      (some (Attr.m {"a"} (fun k => Attr.s "x"))) = .same := rfl

/-- `object_open` -/
theorem object_open :
    check 2
      ((denote (Term.object (Body.mk {"a"} (fun k => ObjectSlot.req (Term.string)) (some (Term.boolean))))).e
        (Value.map {"a", "z"} (fun k => if k.1 = "a" then Value.str "x" else Value.bool true)))
      (some (Attr.m {"a", "z"} (fun k => if k.1 = "a" then Attr.s "x" else Attr.bool true))) = .same := rfl

/-- `object_nested` -/
theorem object_nested :
    check 3
      ((denote (Term.object (Body.mk {"a"} (fun k => ObjectSlot.req (Term.object (Body.mk {"b"} (fun k => ObjectSlot.req (Term.string)) none))) none))).e
        (Value.map {"a"} (fun k => Value.map {"b"} (fun k => Value.str "x"))))
      (some (Attr.m {"a"} (fun k => Attr.m {"b"} (fun k => Attr.s "x")))) = .same := rfl

/-- `open_of_restricted_set` -/
theorem open_of_restricted_set :
    check 2
      ((denote (Term.object (Body.mk ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)) (some (Term.refine (Term.set SetBase.string) (Pred.each (Pred.members GroundKind.string (NEFinset.of "a" {"b"})))))))).e
        (Value.map {"a"} (fun k => Value.strSet (NEFinset.of "a" ∅))))
      (some (Attr.m {"a"} (fun k => Attr.ss (NEFinset.of "a" ∅)))) = .same := rfl

/-- `object_restricted_rest` -/
theorem object_restricted_rest :
    check 2
      ((denote (Term.object (Body.mk {"a"} (fun k => ObjectSlot.req (Term.refine (Term.set SetBase.string) (Pred.each (Pred.members GroundKind.string (NEFinset.of "b" {"c"}))))) (some (Term.refine (Term.set SetBase.string) (Pred.each (Pred.members GroundKind.string (NEFinset.of "b" {"c"})))))))).e
        (Value.map {"a", "z"} (fun k => if k.1 = "a" then Value.strSet (NEFinset.of "b" ∅) else Value.strSet (NEFinset.of "c" ∅))))
      (some (Attr.m {"a", "z"} (fun k => if k.1 = "a" then Attr.ss (NEFinset.of "b" ∅) else Attr.ss (NEFinset.of "c" ∅)))) = .same := rfl

/-- `map_inside_a_list` -/
theorem map_inside_a_list :
    check 3
      ((denote (Term.array (Term.object (Body.mk ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)) (some (Term.string)))))).e
        (Value.arr [Value.map {"a"} (fun k => Value.str "x")]))
      (some (Attr.l [Attr.m {"a"} (fun k => Attr.s "x")])) = .same := rfl

/-- `union_of_two` -/
theorem union_of_two :
    check 1
      ((denote (Term.union [Term.string, Term.boolean])).e
        (Value.bool true))
      (some (Attr.bool true)) = .same := rfl

/-- `nullable_null` -/
theorem nullable_null :
    check 1
      ((denote (Term.union [Term.string, Term.null])).e
        (Value.null))
      (some (Attr.null)) = .same := rfl

/-- `union_by_literal` -/
theorem union_by_literal :
    check 2
      ((denote (Term.union [Term.object (Body.mk {"kind", "x"} (fun k => if k.1 = "kind" then ObjectSlot.req (Term.literal GroundKind.string "a") else ObjectSlot.req (Term.string)) none), Term.object (Body.mk {"kind", "x"} (fun k => if k.1 = "kind" then ObjectSlot.req (Term.literal GroundKind.string "b") else ObjectSlot.req (Term.boolean)) none)])).e
        (Value.map {"kind", "x"} (fun k => if k.1 = "kind" then Value.str "a" else Value.str "v")))
      (some (Attr.m {"kind", "x"} (fun k => if k.1 = "kind" then Attr.s "a" else Attr.s "v"))) = .same := rfl

/-- `discriminated_union` -/
theorem discriminated_union :
    check 2
      ((denote (Term.union [Term.object (Body.mk {"kind", "x"} (fun k => if k.1 = "kind" then ObjectSlot.req (Term.literal GroundKind.string "a") else ObjectSlot.req (Term.string)) none), Term.object (Body.mk {"kind", "y"} (fun k => if k.1 = "kind" then ObjectSlot.req (Term.literal GroundKind.string "b") else ObjectSlot.req (Term.boolean)) none)])).e
        (Value.map {"kind", "x"} (fun k => if k.1 = "kind" then Value.str "a" else Value.str "v")))
      (some (Attr.m {"kind", "x"} (fun k => if k.1 = "kind" then Attr.s "a" else Attr.s "v"))) = .same := rfl

/-- `product_two_objects` -/
theorem product_two_objects :
    check 2
      ((denote (Term.object (Body.mk {"a", "n"} (fun k => if k.1 = "a" then ObjectSlot.req (Term.string) else ObjectSlot.req (Term.boolean)) none))).e
        (Value.map {"a", "n"} (fun k => if k.1 = "a" then Value.str "x" else Value.bool true)))
      (some (Attr.m {"a", "n"} (fun k => if k.1 = "a" then Attr.s "x" else Attr.bool true))) = .same := rfl

/-- `product_union_object` -/
theorem product_union_object :
    check 2
      ((denote (Term.union [Term.object (Body.mk {"a", "n"} (fun k => if k.1 = "a" then ObjectSlot.req (Term.string) else ObjectSlot.req ((Term.held (Term.number) numeralOfStoredText textOfNumeral))) none), Term.object (Body.mk {"b", "n"} (fun k => if k.1 = "b" then ObjectSlot.req (Term.boolean) else ObjectSlot.req ((Term.held (Term.number) numeralOfStoredText textOfNumeral))) none)])).e
        (Value.map {"a", "n"} (fun k => if k.1 = "a" then Value.str "x" else Value.str "1")))
      (some (Attr.m {"a", "n"} (fun k => if k.1 = "a" then Attr.s "x" else Attr.n (WFNumeral.of "1")))) = .same := rfl

/-- `product_three` -/
theorem product_three :
    check 2
      ((denote (Term.object (Body.mk {"p", "q", "r"} (fun k => if k.1 = "p" then ObjectSlot.req (Term.string) else if k.1 = "q" then ObjectSlot.req (Term.boolean) else ObjectSlot.req ((Term.held (Term.number) numeralOfStoredText textOfNumeral))) none))).e
        (Value.map {"p", "q", "r"} (fun k => if k.1 = "p" then Value.str "x" else if k.1 = "q" then Value.bool true else Value.str "1")))
      (some (Attr.m {"p", "q", "r"} (fun k => if k.1 = "p" then Attr.s "x" else if k.1 = "q" then Attr.bool true else Attr.n (WFNumeral.of "1")))) = .same := rfl

/-- `dunion_two_keys` -/
theorem dunion_two_keys :
    check 2
      ((denote (Term.union [Term.object (Body.mk {"kind", "size", "toy"} (fun k => if k.1 = "kind" then ObjectSlot.req (Term.literal GroundKind.string "pet") else if k.1 = "size" then ObjectSlot.req (Term.literal GroundKind.string "small") else ObjectSlot.req (Term.string)) none), Term.object (Body.mk {"kind", "size", "pen"} (fun k => if k.1 = "kind" then ObjectSlot.req (Term.literal GroundKind.string "pet") else if k.1 = "size" then ObjectSlot.req (Term.literal GroundKind.string "large") else ObjectSlot.req (Term.string)) none)])).e
        (Value.map {"kind", "size", "toy"} (fun k => if k.1 = "kind" then Value.str "pet" else if k.1 = "size" then Value.str "small" else Value.str "ball")))
      (some (Attr.m {"kind", "size", "toy"} (fun k => if k.1 = "kind" then Attr.s "pet" else if k.1 = "size" then Attr.s "small" else Attr.s "ball"))) = .same := rfl

/-- `opaque_map` -/
theorem opaque_map :
    check 2
      ((denote (Term.opaq false)).e
        (Value.map {"a"} (fun k => Value.str "x")))
      (some (Attr.m {"a"} (fun k => Attr.s "x"))) = .same := rfl

/-- `lazy_string` -/
theorem lazy_string :
    check 1
      ((denote (Term.lazy (Term.string))).e
        (Value.str "x"))
      (some (Attr.s "x")) = .same := rfl

/-! ### Read back, through the same term

The model's `p`, given the attribute the library wrote, against the value the library read. Only
the `check` sample carries these: a read vector's answer is a `Value`, so it needs `vcheck`, and
the `equation` sample depends on nothing beyond `denote` by design. -/

/-- `scalar_string` — read back through the term that wrote it -/
theorem scalar_string__reads :
    vcheck 1
      ((denote (Term.string)).p
        (Attr.s "hello"))
      (some (Value.str "hello")) = .same := rfl

/-- `scalar_boolean` — read back through the term that wrote it -/
theorem scalar_boolean__reads :
    vcheck 1
      ((denote (Term.boolean)).p
        (Attr.bool true))
      (some (Value.bool true)) = .same := rfl

/-- `set_of_string` — read back through the term that wrote it -/
theorem set_of_string__reads :
    vcheck 1
      ((denote (Term.set SetBase.string)).p
        (Attr.ss (NEFinset.of "a" {"b"})))
      (some (Value.strSet (NEFinset.of "a" {"b"}))) = .same := rfl

/-- `array_of_string` — read back through the term that wrote it -/
theorem array_of_string__reads :
    vcheck 2
      ((denote (Term.array (Term.string))).p
        (Attr.l [Attr.s "a", Attr.s "b"]))
      (some (Value.arr [Value.str "a", Value.str "b"])) = .same := rfl

/-- `object_two_fields` — read back through the term that wrote it -/
theorem object_two_fields__reads :
    vcheck 2
      ((denote (Term.object (Body.mk {"a", "b"} (fun k => if k.1 = "a" then ObjectSlot.req (Term.string) else ObjectSlot.req (Term.boolean)) none))).p
        (Attr.m {"a", "b"} (fun k => if k.1 = "a" then Attr.s "x" else Attr.bool true)))
      (some (Value.map {"a", "b"} (fun k => if k.1 = "a" then Value.str "x" else Value.bool true))) = .same := rfl

/-- `union_of_two` — read back through the term that wrote it -/
theorem union_of_two__reads :
    vcheck 1
      ((denote (Term.union [Term.string, Term.boolean])).p
        (Attr.bool true))
      (some (Value.bool true)) = .same := rfl

/-! ## Refusals — neither side writes anything for these

38 of 1267 shown; `scripts/gate.sh` elaborates all
1267. One `rfl` each, no comparator and no fuel: the answer is `none`,
which carries no function for the funext gap to open under.
-/

/-- `scalar_string__refuses__scalar_boolean` — refused on both sides -/
theorem scalar_string__refuses__scalar_boolean :
    (denote (Term.string)).e
      (Value.bool true) = none := rfl

/-- `scalar_decimal__refuses__scalar_string` — refused on both sides -/
theorem scalar_decimal__refuses__scalar_string :
    (denote ((Term.held (Term.number) numeralOfStoredText textOfNumeral))).e
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
    (denote ((Term.held (Term.union [Term.literal GroundKind.number (WFNumeral.of "1"), Term.literal GroundKind.number (WFNumeral.of "2.5")]) numeralOfStoredText textOfNumeral))).e
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
    (denote (Term.set SetBase.string)).e
      (Value.str "hello") = none := rfl

/-- `set_of_literal__refuses__scalar_string` — refused on both sides -/
theorem set_of_literal__refuses__scalar_string :
    (denote (Term.refine (Term.set SetBase.string) (Pred.each (Pred.members GroundKind.string (NEFinset.of "a" {"b"}))))).e
      (Value.str "hello") = none := rfl

/-- `set_of_number__refuses__scalar_string` — refused on both sides -/
theorem set_of_number__refuses__scalar_string :
    (denote (Term.set SetBase.number)).e
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
    (denote (Term.object (Body.mk ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)) (some (Term.refine (Term.set SetBase.string) (Pred.each (Pred.members GroundKind.string (NEFinset.of "a" {"b"})))))))).e
      (Value.str "hello") = none := rfl

/-- `object_restricted_rest__refuses__scalar_string` — refused on both sides -/
theorem object_restricted_rest__refuses__scalar_string :
    (denote (Term.object (Body.mk {"a"} (fun k => ObjectSlot.req (Term.refine (Term.set SetBase.string) (Pred.each (Pred.members GroundKind.string (NEFinset.of "b" {"c"}))))) (some (Term.refine (Term.set SetBase.string) (Pred.each (Pred.members GroundKind.string (NEFinset.of "b" {"c"})))))))).e
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
    (denote (Term.union [Term.object (Body.mk {"a", "n"} (fun k => if k.1 = "a" then ObjectSlot.req (Term.string) else ObjectSlot.req ((Term.held (Term.number) numeralOfStoredText textOfNumeral))) none), Term.object (Body.mk {"b", "n"} (fun k => if k.1 = "b" then ObjectSlot.req (Term.boolean) else ObjectSlot.req ((Term.held (Term.number) numeralOfStoredText textOfNumeral))) none)])).e
      (Value.str "hello") = none := rfl

/-- `product_three__refuses__scalar_string` — refused on both sides -/
theorem product_three__refuses__scalar_string :
    (denote (Term.object (Body.mk {"p", "q", "r"} (fun k => if k.1 = "p" then ObjectSlot.req (Term.string) else if k.1 = "q" then ObjectSlot.req (Term.boolean) else ObjectSlot.req ((Term.held (Term.number) numeralOfStoredText textOfNumeral))) none))).e
      (Value.str "hello") = none := rfl

/-- `dunion_two_keys__refuses__scalar_string` — refused on both sides -/
theorem dunion_two_keys__refuses__scalar_string :
    (denote (Term.union [Term.object (Body.mk {"kind", "size", "toy"} (fun k => if k.1 = "kind" then ObjectSlot.req (Term.literal GroundKind.string "pet") else if k.1 = "size" then ObjectSlot.req (Term.literal GroundKind.string "small") else ObjectSlot.req (Term.string)) none), Term.object (Body.mk {"kind", "size", "pen"} (fun k => if k.1 = "kind" then ObjectSlot.req (Term.literal GroundKind.string "pet") else if k.1 = "size" then ObjectSlot.req (Term.literal GroundKind.string "large") else ObjectSlot.req (Term.string)) none)])).e
      (Value.str "hello") = none := rfl

/-- `opaque_map__refuses__set_of_number` — refused on both sides -/
theorem opaque_map__refuses__set_of_number :
    (denote (Term.opaq false)).e
      (Value.numSet (NEFinset.of (WFNumeral.of "1.5") {(WFNumeral.of "2")})) = none := rfl

/-- `lazy_string__refuses__scalar_boolean` — refused on both sides -/
theorem lazy_string__refuses__scalar_boolean :
    (denote (Term.lazy (Term.string))).e
      (Value.bool true) = none := rfl

/-- `scalar_number__refuses__scalar_string` — refused on both sides -/
theorem scalar_number__refuses__scalar_string :
    (denote (Term.number)).e
      (Value.str "hello") = none := rfl

/-- `never__refuses__scalar_string` — refused on both sides -/
theorem never__refuses__scalar_string :
    (denote (Term.never)).e
      (Value.str "hello") = none := rfl

end Calculus
