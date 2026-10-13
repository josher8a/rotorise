import Calculus.Dynamo.Analysis.ScopeSeparation

/-!
# What the set and map carriers record

A set and a map carry no order and no repeat, and the type states both facts. The separation
results over closed codecs live in `Dynamo/Analysis/ScopeSeparation.lean`.
-/

namespace Calculus

section
/-! ### What `set` is, structurally

Three readings are worth separating. The third is a fact about the type, and the theorems
below are its witnesses.

**Not a `union`.** A union is a choice among *codecs*, lawful by pairwise compatibility; a
set's elements all go through **one** codec, so no obligation between codecs arises. That is
why `set` needs no compatibility premise and `union` does.

**Not `array` with a wrapper.** `array` traverses a `List Value`, and `set` images a
`Finset`. The two share the *element* codec and nothing else.

**"Order does not matter" is true of the model.** `SS` has the type `℘⁺fin(String)`, and the
reference says the order of a set's values is not preserved and each value is unique. The
three theorems below state it: an ordering is not a distinction a `Finset` can make, and a
repeat is not an inhabitant it can hold. -/

/-- Two "orderings" of one set are the same value — there is nothing to quotient. -/
theorem set_order_irrelevant :
    (Value.strSet (.of "a" {"b"})) = (Value.strSet (.of "b" {"a"})) :=
  congrArg Value.strSet (Subtype.ext (Finset.ext fun x => by
    simp only [NEFinset.of, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun h => h.elim (fun e => Or.inr e) (fun e => Or.inl e),
           fun h => h.elim (fun e => Or.inr e) (fun e => Or.inl e)⟩))

/-- …and the same attribute. -/
theorem wireSet_order_irrelevant :
    (Attr.ss (.of "a" {"b"})) = (Attr.ss (.of "b" {"a"})) :=
  congrArg Attr.ss (Subtype.ext (Finset.ext fun x => by
    simp only [NEFinset.of, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun h => h.elim (fun e => Or.inr e) (fun e => Or.inl e),
           fun h => h.elim (fun e => Or.inr e) (fun e => Or.inl e)⟩))

/-- A repeat is not an inhabitant: `℘⁺fin` has no multiplicities, and neither does the
    model. -/
theorem set_no_duplicates :
    (Value.strSet (.of "a" {"a"})) = (Value.strSet (.of "a" ∅)) :=
  congrArg Value.strSet (Subtype.ext (Finset.ext fun x => by
    simp only [NEFinset.of, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, or_false]
    exact ⟨fun h => h.elim id id, fun h => Or.inl h⟩))

/-! ### What (R) forces on a list carrier for a set

(R) makes `e` injective, so a list-carried set codec cannot normalise: two spellings of one set
that write one attribute owe that attribute two readings. (R) does not rule out a canonical form.
A list carrier with a decidable total order on `Value` is lawful when `e` accepts only the
canonical spelling and refuses the rest, and `p` returns the canonical spelling. The cost is the
refusal: every set codec refuses a non-canonical spelling, so the carrier holds values that no set
codec writes.

`Finset` has one representative per set *as a type*, so there is nothing for `e` to refuse and
nothing for `p` to choose, and `ker p` is equality at `setCodec`. The kernel refuses the generic
carrier (a nested `Finset`, `Multiset` or `Quot` of the datatype being declared), which is why the
three concrete set carriers stay.

No canonical form and no order is on the set path or on the map path. The quotient the kernel
refuses is `Finset (Name × Attr)`, and `M` does not need it, as the next section shows. -/

/-! ### The reference, checked against the model

`docs/dynamo-datatypes.md` is the official datatype reference. Most of the attribute domain survives it
exactly — `Numeral.WF`'s 38 digits and `-130 … 125` exponent range are the documented
bounds; binary compares unsigned; empty strings and empty binary are permitted, empty lists
and maps are permitted, empty sets are not, and the model already refuses the last.

Two statements of the reference are about order and uniqueness, and the type carries both.

**`SS`/`NS`/`BS`**: *"Each value within a set must be unique. The order of the values within
a set is not preserved."* The section above states it.

**`M`**: *"A map type attribute can store an **unordered** collection of name-value
pairs."* The three theorems below state it.

**A map is typed, not gated.** `Finset (Name × Attr)` is rejected by the kernel, exactly as
`Finset Value` is, because the element type is the one under declaration. That does not send
`M` to a well-formedness premise. The pair need not be the element: `M` is a finite
*partial function*, so the names go in a `Finset` over the concrete type `Name` and the
attributes go in a function's codomain, a strictly positive position that the kernel accepts:

    | m (keys : Finset Name) (f : {k // k ∈ keys} → Attr)

Unordered, unique-keyed and total-on-its-keys are facts about the type. No canonical order
exists, and `e` has nothing to choose between. -/

/-- Two "orderings" of one map's names are one name set — there is nothing to quotient. -/
theorem mapKeys_order_irrelevant : ({"a", "b"} : Finset Name) = {"b", "a"} :=
  Finset.ext fun x => by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun h => h.elim (fun e => Or.inr e) (fun e => Or.inl e),
           fun h => h.elim (fun e => Or.inr e) (fun e => Or.inl e)⟩

/-- …so the codec has one answer. Equal key sets and pointwise-equal entries are one
    attribute (`MapOf.ext`), and one attribute is one reading, so no reading depends on an
    order. -/
theorem record_p_order_irrelevant
    (g : {k // k ∈ ({"a", "b"} : Finset Name)} → Attr)
    (g' : {k // k ∈ ({"b", "a"} : Finset Name)} → Attr)
    (h : ∀ k (h₁ : k ∈ ({"a", "b"} : Finset Name)) (h₂ : k ∈ ({"b", "a"} : Finset Name)),
      g ⟨k, h₁⟩ = g' ⟨k, h₂⟩) :
    (recordCodec (baseCodec .string)).p (.m {"a", "b"} g)
      = (recordCodec (baseCodec .string)).p (.m {"b", "a"} g') :=
  congrArg (fun p : MapOf Attr => (recordCodec (baseCodec .string)).p (.m p.1 p.2))
    (MapOf.ext (p := ⟨{"a", "b"}, g⟩) (q := ⟨{"b", "a"}, g'⟩) mapKeys_order_irrelevant h)

/-- A repeated key is not an inhabitant: the map that was supposed to carry `"a"` twice is
    the map that carries it once. -/
theorem mapKeys_no_duplicates : ({"a", "a"} : Finset Name) = {"a"} :=
  Finset.ext fun x => by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun h => h.elim id id, fun h => Or.inr h⟩

end



end Calculus
