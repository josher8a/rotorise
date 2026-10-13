import Calculus.Dynamo.Analysis.ScopeSlice
import Calculus.Dynamo.Analysis.ScopeOrthogonality

/-!
# Worked pairs of the disjointness decision over closed codecs

Each pair below is a pair of closed codecs, and the kernel checks the verdict of `Closed.disjoint`,
of `Closed.viewsDisjoint` or of `certAllC`. A refinement or a `held` over a recursive codec reads
the recursion as a constant of an earlier scope (`Closed.over`), so the recursion keeps its own
entry below the refinement.

A certified union is separated (`Closed.separated_of_certAllC`): no value has two writers, and no
attribute has two readers.
-/

namespace Calculus

/-- **A closed codec of two scopes**: the first scope holds `base` as its one entry, and the root
    entry `top` reads that entry as the constant `0`. -/
def Closed.over (base : Scoped.Term 0 1 0) (top : Scoped.Term 1 1 0) : Closed :=
  ⟨2, .snoc (c := 1) (n := 1) (.snoc (c := 0) (n := 1) .nil
    (fun i => match i with | ⟨0, _⟩ => base)) (fun i => match i with | ⟨0, _⟩ => top), 1⟩

/-- A recursive codec: a boolean, or an object whose key `"k"` holds the codec again. -/
def recBoolBody : Scoped.Term 0 1 0 :=
  .union [.boolean, .object (Scoped.Body.mk {"k"} (fun _ => .req (.ref 0)) none)]

/-- A recursive codec: a string, or an object whose key `"k"` holds the codec again. -/
def recStrBody : Scoped.Term 0 1 0 :=
  .union [.string, .object (Scoped.Body.mk {"k"} (fun _ => .req (.ref 0)) none)]

/-! ## Refinements and recursion -/

/-- **A refinement is apart from a refined union in both orders.** The right union refines
    `literal "a" ∪ number` to `literal "b"`, and the decision reads the predicate of the right
    refinement on each option below the refinement. -/
theorem Closed.disjoint_refinedUnion_bothOrders :
    (Closed.one (.refine .string (.members .string (NEFinset.of "b" ∅)) ())).disjoint
      (Closed.one (.union [.refine (.union [.refine .string (.members .string (NEFinset.of "a" ∅)) (),
          .number]) (.members .string (NEFinset.of "b" ∅)) (), .number])) = true ∧
    (Closed.one (.union [.refine (.union [.refine .string (.members .string (NEFinset.of "a" ∅)) (),
          .number]) (.members .string (NEFinset.of "b" ∅)) (), .number])).disjoint
      (Closed.one (.refine .string (.members .string (NEFinset.of "b" ∅)) ())) = true := by
  decide

/-- **Two recursive codecs are apart in both orders where a refinement covers one.** A tree of
    booleans and a refined tree of strings share no value. -/
theorem Closed.disjoint_refinedRecursion_bothOrders :
    (Closed.one recBoolBody).disjoint
      (Closed.over recStrBody (.refine (.const 0) (.closure fun _ => true) ())) = true ∧
    (Closed.over recStrBody (.refine (.const 0) (.closure fun _ => true) ())).disjoint
      (Closed.one recBoolBody) = true := by
  decide

/-- **The certificate of a union does not read the order of the options.** A recursive codec
    beside a `held` over a refined recursive codec is certified in both orders. -/
theorem Closed.viewsDisjoint_heldRecursion_bothOrders :
    (Closed.one recBoolBody).viewsDisjoint
      (Closed.over recStrBody
        (.held false .string (.refine (.const 0) (.closure fun _ => true) ()) (.caller 0, false) [])) = true ∧
    (Closed.over recStrBody
        (.held false .string (.refine (.const 0) (.closure fun _ => true) ()) (.caller 0, false) [])).viewsDisjoint
      (Closed.one recBoolBody) = true := by
  decide

/-! ## Arrays told apart by a literal position

The owner's witness. Each list starts with a literal, and the empty list is an option of its own. -/

/-- The three options: a nonempty list of `"A"`, a nonempty list of `"B"`, and the empty list. -/
def literalListOptionsC : List Closed :=
  [Closed.one (.list [.literal .string "A"] (some (.literal .string "A")) []),
   Closed.one (.list [.literal .string "B"] (some (.literal .string "B")) []),
   Closed.one (.list [] none [])]

/-- **The certificate certifies the union**: each pair of options is disjoint. -/
theorem Closed.certAllC_literalListOptions : certAllC literalListOptionsC = true := by decide

/-- **The crossing control is not certified.** `array (literal "A")` and `array (literal "B")`
    both hold `[]`. -/
theorem Closed.not_certAllC_literalArrays :
    certAllC [Closed.one (.array (.literal .string "A")),
      Closed.one (.array (.literal .string "B"))] = false := by
  decide

/-! ## Two restricted sets, apart at their elements -/

/-- **Two string sets with disjoint members are disjoint.** No set is empty. -/
theorem Closed.disjoint_disjointStringSets :
    (Closed.one (.set (.refine .string (.members .string (NEFinset.of "a" {"b"})) ()))).disjoint
      (Closed.one (.set (.refine .string (.members .string (NEFinset.of "c" ∅)) ()))) = true := by
  decide

/-- **Two string sets that share a member are not disjoint.** -/
theorem Closed.not_disjoint_stringSets_shared :
    (Closed.one (.set (.refine .string (.members .string (NEFinset.of "a" {"b"})) ()))).disjoint
      (Closed.one (.set (.refine .string (.members .string (NEFinset.of "b" {"c"})) ()))) = false := by
  decide

/-! ## The views certify a `held` whose caller side is precise

A string set held as a list of strings, beside a list of numbers. Both codecs write a list, and the
decision does not read a raw `held`. The caller-side views are disjoint when the caller side
requires one element or more, and the stored-side views differ in kind. -/

/-- The decision on the two codecs does not certify the pair. -/
theorem Closed.disjoint_heldNE_base :
    (Closed.one (.held false (.set .string) (.list [.string] (some .string) []) (.caller 0, false) [])).disjoint
      (Closed.one (.list [] (some .number) [])) = false := by
  decide

/-- **A caller side that requires one element or more is certified** beside a list of numbers. -/
theorem Closed.viewsDisjoint_heldNE :
    (Closed.one (.held false (.set .string) (.list [.string] (some .string) []) (.caller 0, false) [])).viewsDisjoint
      (Closed.one (.list [] (some .number) [])) = true := by
  decide

/-- **A caller side that admits the empty list is refused**, because the list of numbers admits
    the empty list too. -/
theorem Closed.viewsDisjoint_heldAny :
    (Closed.one (.held false (.set .string) (.list [] (some .string) []) (.caller 0, false) [])).viewsDisjoint
      (Closed.one (.list [] (some .number) [])) = false := by
  decide

/-- **A `held` below a recursion is certified where the views part.** The caller view of the
    recursive codec holds `literal "1"` and lists of itself, and the stored view holds `number` and
    lists of itself. Each view is disjoint from `literal "A" ∪ literal "B"`. -/
theorem Closed.viewsDisjoint_heldBelowMu :
    (Closed.one (.union [.literal .string "A", .literal .string "B"])).viewsDisjoint
      (Closed.one (.union [.held false .number (.literal .string "1") (.caller 0, false) [],
        .list [] (some (.ref 0)) []])) = true := by
  decide

/-- …and the pair is refused where the caller views share a value: the text `"1"`. -/
theorem Closed.viewsDisjoint_heldBelowMu_meets :
    (Closed.one (.literal .string "1")).viewsDisjoint
      (Closed.one (.union [.held false .number (.literal .string "1") (.caller 0, false) [],
        .list [] (some (.ref 0)) []])) = false := by
  decide

/-! ## A certified union is separated -/

variable {α : Table}

/-- **A certified union is separated**, which is the premise of
    `Closed.pairwiseCompat_of_separated` and of `Closed.admitsAtMostOne_of_separated`. -/
theorem Closed.separated_of_certAllC {os : List Closed} (h : certAllC os = true) :
    Closed.Separated α os :=
  (pairwise_of_certAllC h).imp fun hxy => by
    refine ⟨fun v hx hy => ?_, fun a hx hy => ?_⟩
    · have := (Closed.viewsDisjoint_sound hxy α).1 v
      rw [hx, hy] at this; exact nomatch this
    · have := (Closed.viewsDisjoint_sound hxy α).2 a
      rw [← Closed.AdmA_eq_isSome, ← Closed.AdmA_eq_isSome, hx, hy] at this; exact nomatch this

end Calculus
