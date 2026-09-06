import Calculus.Vectors

/-!
# Differential-testing vectors

**Generated — do not edit.** Emitted by `src/lean.ts` from the shipped TypeScript codecs: each
theorem below is one `encode` this library actually performed, proposed to the model. A failure
here is a disagreement between `src/codec.ts` and `Calculus.denote`, and the theorem's name says
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
      ((denote (Term.decimal)).e
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
      ((denote (Term.literal GroundKind.string (NEFinset.of "A" {"B"}))).e
        (Value.str "B"))
      (some (Attr.s "B")) = .same := rfl

/-- `literal_decimal` -/
theorem literal_decimal :
    check 1
      ((denote (Term.literal GroundKind.decimal (NEFinset.of ⟨"1", by decide⟩ {⟨"2.5", by decide⟩}))).e
        (Value.str "2.5"))
      (some (Attr.n (WFNumeral.of "2.5"))) = .same := rfl

/-- `literal_binary` -/
theorem literal_binary :
    check 1
      ((denote (Term.literal GroundKind.binary (NEFinset.of [0, 127, 255] ∅))).e
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
      ((denote (Term.refine (Term.set SetBase.string) (liftQ (inL GroundKind.string (NEFinset.of "a" {"b"}))))).e
        (Value.strSet (NEFinset.of "b" {"a"})))
      (some (Attr.ss (NEFinset.of "a" {"b"}))) = .same := rfl

/-- `set_of_decimal` -/
theorem set_of_decimal :
    check 1
      ((denote (Term.set SetBase.decimal)).e
        (Value.strSet (NEFinset.of "1.5" {"2"})))
      (some (Attr.ns (NEFinset.of (WFNumeral.of "1.5") {(WFNumeral.of "2")}))) = .same := rfl

/-- `array_of_string` -/
theorem array_of_string :
    check 2
      ((denote (Term.array (Term.string))).e
        (Value.arr [Value.str "a", Value.str "b"]))
      (some (Attr.l [Attr.s "a", Attr.s "b"])) = .same := rfl

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

/-- `record_of_string` -/
theorem record_of_string :
    check 2
      ((denote (Term.record (Term.string))).e
        (Value.map {"a", "b"} (fun k => if k.1 = "a" then Value.str "x" else Value.str "y")))
      (some (Attr.m {"a", "b"} (fun k => if k.1 = "a" then Attr.s "x" else Attr.s "y"))) = .same := rfl

/-- `record_empty` -/
theorem record_empty :
    check 1
      ((denote (Term.record (Term.string))).e
        (Value.map ∅ (fun k => absurd k.2 (Finset.not_mem_empty k.1))))
      (some (Attr.m ∅ (fun k => absurd k.2 (Finset.not_mem_empty k.1)))) = .same := rfl

/-- `object_two_fields` -/
theorem object_two_fields :
    check 2
      ((denote (Term.object (Body.mk {"a", "b"} (fun k => if k.1 = "a" then Field.req (Term.string) else Field.req (Term.boolean)) Rest.drop))).e
        (Value.map {"a", "b"} (fun k => if k.1 = "a" then Value.str "x" else Value.bool true)))
      (some (Attr.m {"a", "b"} (fun k => if k.1 = "a" then Attr.s "x" else Attr.bool true))) = .same := rfl

/-- `object_optional_absent` -/
theorem object_optional_absent :
    check 2
      ((denote (Term.object (Body.mk {"a", "b"} (fun k => if k.1 = "a" then Field.req (Term.string) else Field.optional (Term.boolean)) Rest.drop))).e
        (Value.map {"a"} (fun k => Value.str "x")))
      (some (Attr.m {"a"} (fun k => Attr.s "x"))) = .same := rfl

/-- `object_fallback_present` -/
theorem object_fallback_present :
    check 2
      ((denote (Term.object (Body.mk {"a"} (fun k => Field.fallback (Term.string) (Value.str "stand-in")) Rest.drop))).e
        (Value.map {"a"} (fun k => Value.str "x")))
      (some (Attr.m {"a"} (fun k => Attr.s "x"))) = .same := rfl

/-- `object_open` -/
theorem object_open :
    check 2
      ((denote (Term.object (Body.mk {"a"} (fun k => Field.req (Term.string)) (Rest.codec (Term.boolean))))).e
        (Value.map {"a", "z"} (fun k => if k.1 = "a" then Value.str "x" else Value.bool true)))
      (some (Attr.m {"a", "z"} (fun k => if k.1 = "a" then Attr.s "x" else Attr.bool true))) = .same := rfl

/-- `object_nested` -/
theorem object_nested :
    check 3
      ((denote (Term.object (Body.mk {"a"} (fun k => Field.req (Term.object (Body.mk {"b"} (fun k => Field.req (Term.string)) Rest.drop))) Rest.drop))).e
        (Value.map {"a"} (fun k => Value.map {"b"} (fun k => Value.str "x"))))
      (some (Attr.m {"a"} (fun k => Attr.m {"b"} (fun k => Attr.s "x")))) = .same := rfl

/-- `map_inside_a_list` -/
theorem map_inside_a_list :
    check 3
      ((denote (Term.array (Term.record (Term.string)))).e
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
      ((denote (Term.nullable (Term.string))).e
        (Value.null))
      (some (Attr.null)) = .same := rfl

/-- `discriminated_union` -/
theorem discriminated_union :
    check 2
      ((denote (Term.dunion "kind" [Term.object (Body.mk {"kind", "x"} (fun k => if k.1 = "kind" then Field.req (Term.literal GroundKind.string (NEFinset.of "a" ∅)) else Field.req (Term.string)) Rest.drop), Term.object (Body.mk {"kind", "y"} (fun k => if k.1 = "kind" then Field.req (Term.literal GroundKind.string (NEFinset.of "b" ∅)) else Field.req (Term.boolean)) Rest.drop)])).e
        (Value.map {"kind", "x"} (fun k => if k.1 = "kind" then Value.str "a" else Value.str "v")))
      (some (Attr.m {"kind", "x"} (fun k => if k.1 = "kind" then Attr.s "a" else Attr.s "v"))) = .same := rfl

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

/-! ## Refusals — neither side writes anything for these

27 of 649 shown; `scripts/gate.sh` elaborates all
649. One `rfl` each, no comparator and no fuel: the answer is `none`,
which carries no function for the funext gap to open under.
-/

/-- `scalar_string__refuses__scalar_boolean` — refused on both sides -/
theorem scalar_string__refuses__scalar_boolean :
    (denote (Term.string)).e
      (Value.bool true) = none := rfl

/-- `scalar_decimal__refuses__scalar_string` — refused on both sides -/
theorem scalar_decimal__refuses__scalar_string :
    (denote (Term.decimal)).e
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
    (denote (Term.literal GroundKind.string (NEFinset.of "A" {"B"}))).e
      (Value.str "hello") = none := rfl

/-- `literal_decimal__refuses__scalar_string` — refused on both sides -/
theorem literal_decimal__refuses__scalar_string :
    (denote (Term.literal GroundKind.decimal (NEFinset.of ⟨"1", by decide⟩ {⟨"2.5", by decide⟩}))).e
      (Value.str "hello") = none := rfl

/-- `literal_binary__refuses__scalar_string` — refused on both sides -/
theorem literal_binary__refuses__scalar_string :
    (denote (Term.literal GroundKind.binary (NEFinset.of [0, 127, 255] ∅))).e
      (Value.str "hello") = none := rfl

/-- `set_of_string__refuses__scalar_string` — refused on both sides -/
theorem set_of_string__refuses__scalar_string :
    (denote (Term.set SetBase.string)).e
      (Value.str "hello") = none := rfl

/-- `set_of_literal__refuses__scalar_string` — refused on both sides -/
theorem set_of_literal__refuses__scalar_string :
    (denote (Term.refine (Term.set SetBase.string) (liftQ (inL GroundKind.string (NEFinset.of "a" {"b"}))))).e
      (Value.str "hello") = none := rfl

/-- `set_of_decimal__refuses__scalar_string` — refused on both sides -/
theorem set_of_decimal__refuses__scalar_string :
    (denote (Term.set SetBase.decimal)).e
      (Value.str "hello") = none := rfl

/-- `array_of_string__refuses__scalar_string` — refused on both sides -/
theorem array_of_string__refuses__scalar_string :
    (denote (Term.array (Term.string))).e
      (Value.str "hello") = none := rfl

/-- `array_empty__refuses__scalar_string` — refused on both sides -/
theorem array_empty__refuses__scalar_string :
    (denote (Term.array (Term.string))).e
      (Value.str "hello") = none := rfl

/-- `tuple_pair__refuses__scalar_string` — refused on both sides -/
theorem tuple_pair__refuses__scalar_string :
    (denote (Term.tuple [Term.string, Term.boolean] none)).e
      (Value.str "hello") = none := rfl

/-- `record_of_string__refuses__scalar_string` — refused on both sides -/
theorem record_of_string__refuses__scalar_string :
    (denote (Term.record (Term.string))).e
      (Value.str "hello") = none := rfl

/-- `record_empty__refuses__scalar_string` — refused on both sides -/
theorem record_empty__refuses__scalar_string :
    (denote (Term.record (Term.string))).e
      (Value.str "hello") = none := rfl

/-- `object_two_fields__refuses__scalar_string` — refused on both sides -/
theorem object_two_fields__refuses__scalar_string :
    (denote (Term.object (Body.mk {"a", "b"} (fun k => if k.1 = "a" then Field.req (Term.string) else Field.req (Term.boolean)) Rest.drop))).e
      (Value.str "hello") = none := rfl

/-- `object_optional_absent__refuses__scalar_string` — refused on both sides -/
theorem object_optional_absent__refuses__scalar_string :
    (denote (Term.object (Body.mk {"a", "b"} (fun k => if k.1 = "a" then Field.req (Term.string) else Field.optional (Term.boolean)) Rest.drop))).e
      (Value.str "hello") = none := rfl

/-- `object_fallback_present__refuses__scalar_string` — refused on both sides -/
theorem object_fallback_present__refuses__scalar_string :
    (denote (Term.object (Body.mk {"a"} (fun k => Field.fallback (Term.string) (Value.str "stand-in")) Rest.drop))).e
      (Value.str "hello") = none := rfl

/-- `object_open__refuses__scalar_string` — refused on both sides -/
theorem object_open__refuses__scalar_string :
    (denote (Term.object (Body.mk {"a"} (fun k => Field.req (Term.string)) (Rest.codec (Term.boolean))))).e
      (Value.str "hello") = none := rfl

/-- `object_nested__refuses__scalar_string` — refused on both sides -/
theorem object_nested__refuses__scalar_string :
    (denote (Term.object (Body.mk {"a"} (fun k => Field.req (Term.object (Body.mk {"b"} (fun k => Field.req (Term.string)) Rest.drop))) Rest.drop))).e
      (Value.str "hello") = none := rfl

/-- `map_inside_a_list__refuses__scalar_string` — refused on both sides -/
theorem map_inside_a_list__refuses__scalar_string :
    (denote (Term.array (Term.record (Term.string)))).e
      (Value.str "hello") = none := rfl

/-- `union_of_two__refuses__scalar_binary` — refused on both sides -/
theorem union_of_two__refuses__scalar_binary :
    (denote (Term.union [Term.string, Term.boolean])).e
      (Value.bin [0, 127, 255]) = none := rfl

/-- `nullable_null__refuses__scalar_boolean` — refused on both sides -/
theorem nullable_null__refuses__scalar_boolean :
    (denote (Term.nullable (Term.string))).e
      (Value.bool true) = none := rfl

/-- `discriminated_union__refuses__scalar_string` — refused on both sides -/
theorem discriminated_union__refuses__scalar_string :
    (denote (Term.dunion "kind" [Term.object (Body.mk {"kind", "x"} (fun k => if k.1 = "kind" then Field.req (Term.literal GroundKind.string (NEFinset.of "a" ∅)) else Field.req (Term.string)) Rest.drop), Term.object (Body.mk {"kind", "y"} (fun k => if k.1 = "kind" then Field.req (Term.literal GroundKind.string (NEFinset.of "b" ∅)) else Field.req (Term.boolean)) Rest.drop)])).e
      (Value.str "hello") = none := rfl

/-- `lazy_string__refuses__scalar_boolean` — refused on both sides -/
theorem lazy_string__refuses__scalar_boolean :
    (denote (Term.lazy (Term.string))).e
      (Value.bool true) = none := rfl

/-- `scalar_number__refuses__scalar_string` — refused on both sides -/
theorem scalar_number__refuses__scalar_string :
    (denote (Term.number)).e
      (Value.str "hello") = none := rfl

end Calculus
