import Calculus.Denote
import Calculus.Combinators
import Mathlib.Tactic.FinCases

/-!
# Differential-testing vectors

**Generated — do not edit.** Emitted by `src/lean.ts` from the shipped TypeScript codecs: each
theorem below is one `encode` this library actually performed, proposed to the model as an
equation. A failure here is a disagreement between `src/codec.ts` and `Calculus.denote`, and the
theorem's name says which vector.
-/

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
    (denote (Term.decimal)).e
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
    (denote (Term.literal GroundKind.string (NEFinset.of "A" {"B"}))).e
      (Value.str "B")
    = some (Attr.s "B") := by
  vector

/-- `literal_decimal` -/
theorem literal_decimal :
    (denote (Term.literal GroundKind.decimal (NEFinset.of ⟨"1", by decide⟩ {⟨"2.5", by decide⟩}))).e
      (Value.str "2.5")
    = some (Attr.n (WFNumeral.of "2.5")) := by
  vector

/-- `literal_binary` -/
theorem literal_binary :
    (denote (Term.literal GroundKind.binary (NEFinset.of [0, 127, 255] ∅))).e
      (Value.bin [0, 127, 255])
    = some (Attr.b [0, 127, 255]) := by
  vector

/-- `set_of_string` -/
theorem set_of_string :
    (denote (Term.set SetBase.string)).e
      (Value.strSet (NEFinset.of "b" {"a"}))
    = some (Attr.ss (NEFinset.of "a" {"b"})) := by
  vector

/-- `set_of_decimal` -/
theorem set_of_decimal :
    (denote (Term.set SetBase.decimal)).e
      (Value.strSet (NEFinset.of "1.5" {"2"}))
    = some (Attr.ns (NEFinset.of (WFNumeral.of "1.5") {(WFNumeral.of "2")})) := by
  vector

/-- `array_of_string` -/
theorem array_of_string :
    (denote (Term.array (Term.string))).e
      (Value.arr [Value.str "a", Value.str "b"])
    = some (Attr.l [Attr.s "a", Attr.s "b"]) := by
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

/-- `record_of_string` -/
theorem record_of_string :
    (denote (Term.record (Term.string))).e
      (Value.map {"a", "b"} (fun k => if k.1 = "a" then Value.str "x" else Value.str "y"))
    = some (Attr.m {"a", "b"} (fun k => if k.1 = "a" then Attr.s "x" else Attr.s "y")) := by
  vector

/-- `record_empty` -/
theorem record_empty :
    (denote (Term.record (Term.string))).e
      (Value.map ∅ (fun k => absurd k.2 (Finset.not_mem_empty k.1)))
    = some (Attr.m ∅ (fun k => absurd k.2 (Finset.not_mem_empty k.1))) := by
  vector

/-- `object_two_fields` -/
theorem object_two_fields :
    (denote (Term.object {"a", "b"} (fun k => if k.1 = "a" then Field.req (Term.string) else Field.req (Term.boolean)) Rest.drop)).e
      (Value.map {"a", "b"} (fun k => if k.1 = "a" then Value.str "x" else Value.bool true))
    = some (Attr.m {"a", "b"} (fun k => if k.1 = "a" then Attr.s "x" else Attr.bool true)) := by
  vector

/-- `object_optional_absent` -/
theorem object_optional_absent :
    (denote (Term.object {"a", "b"} (fun k => if k.1 = "a" then Field.req (Term.string) else Field.optional (Term.boolean)) Rest.drop)).e
      (Value.map {"a"} (fun k => Value.str "x"))
    = some (Attr.m {"a"} (fun k => Attr.s "x")) := by
  vector

/-- `object_fallback_present` -/
theorem object_fallback_present :
    (denote (Term.object {"a"} (fun k => Field.fallback (Term.string) (Value.str "stand-in")) Rest.drop)).e
      (Value.map {"a"} (fun k => Value.str "x"))
    = some (Attr.m {"a"} (fun k => Attr.s "x")) := by
  vector

/-- `object_open` -/
theorem object_open :
    (denote (Term.object {"a"} (fun k => Field.req (Term.string)) (Rest.codec (Term.boolean)))).e
      (Value.map {"a", "z"} (fun k => if k.1 = "a" then Value.str "x" else Value.bool true))
    = some (Attr.m {"a", "z"} (fun k => if k.1 = "a" then Attr.s "x" else Attr.bool true)) := by
  vector

/-- `object_nested` -/
theorem object_nested :
    (denote (Term.object {"a"} (fun k => Field.req (Term.object {"b"} (fun k => Field.req (Term.string)) Rest.drop)) Rest.drop)).e
      (Value.map {"a"} (fun k => Value.map {"b"} (fun k => Value.str "x")))
    = some (Attr.m {"a"} (fun k => Attr.m {"b"} (fun k => Attr.s "x"))) := by
  vector

/-- `map_inside_a_list` -/
theorem map_inside_a_list :
    (denote (Term.array (Term.record (Term.string)))).e
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
    (denote (Term.nullable (Term.string))).e
      (Value.null)
    = some (Attr.null) := by
  vector

/-- `discriminated_union` -/
theorem discriminated_union :
    (denote (Term.dunion "kind" [Term.object {"kind", "x"} (fun k => if k.1 = "kind" then Field.req (Term.literal GroundKind.string (NEFinset.of "a" ∅)) else Field.req (Term.string)) Rest.drop, Term.object {"kind", "y"} (fun k => if k.1 = "kind" then Field.req (Term.literal GroundKind.string (NEFinset.of "b" ∅)) else Field.req (Term.boolean)) Rest.drop])).e
      (Value.map {"kind", "x"} (fun k => if k.1 = "kind" then Value.str "a" else Value.str "v"))
    = some (Attr.m {"kind", "x"} (fun k => if k.1 = "kind" then Attr.s "a" else Attr.s "v")) := by
  vector

/-- `opaque_map` -/
theorem opaque_map :
    (denote (Term.opaq false)).e
      (Value.map {"a"} (fun k => Value.str "x"))
    = some (Attr.m {"a"} (fun k => Attr.s "x")) := by
  vector

/-- `lazy_string` -/
theorem lazy_string :
    (denote (Term.lazy (Term.string))).e
      (Value.str "x")
    = some (Attr.s "x") := by
  vector

end Calculus
