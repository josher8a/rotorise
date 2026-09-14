import Calculus.Typing

/-!
# The merge of two object bodies

The founding operation of the product. A product of two closed objects is the object of
their merged body, and every distribution law above it reduces to this one merge.

Not in `Products.lean`, which is the codec traversal toolkit — `carriedCodec`, `entrywise`,
`tupleCodec` — and reaches `Prisms` rather than `Typing`. This is a syntactic operation on
`Body` with a typing corollary, so it sits with what it is about.
-/

namespace Calculus

/-- Two map payloads over disjoint key sets, as one.

    `Finset.disjUnion` and not `∪`: the union's membership API goes through `Finset.image`
    and `Multiset.dedup`, which reach `Classical.choice`. `disjUnion` carries the proof and
    `Finset.mem_disjUnion` is the whole of its API. -/
def MapOf.disjUnion {α : Type} (a b : MapOf α) (h : Disjoint a.keys b.keys) : MapOf α :=
  { keys := a.keys.disjUnion b.keys h
    get := fun k =>
      if hk : k.1 ∈ a.keys then a.get ⟨k.1, hk⟩
      else b.get ⟨k.1, (Finset.mem_disjUnion.mp k.2).resolve_left hk⟩ }

/-- The rest policies of a product, where there is one. Two closed policies merge, and
    `refuse` wins because a name neither factor declares is a name the product refuses.

    `none` is the refusal, and it is the product declaring no meet of two codecs: an open
    factor holds an undeclared name through a codec of its own, and the product would have
    to hold it through both. -/
def Rest.merge : Rest → Rest → Option Rest
  | .refuse, .refuse => some .refuse
  | .refuse, .drop => some .refuse
  | .drop, .refuse => some .refuse
  | .drop, .drop => some .drop
  | .codec _, _ => none
  | _, .codec _ => none

/-- The body of a product: the disjoint union of the field tables, at the merged policy. -/
def Body.merge (a b : Body) (h : Disjoint a.fields b.fields) {r : Rest}
    (_hr : Rest.merge a.rest b.rest = some r) : Body :=
  .mk (a.fields.disjUnion b.fields h)
    (fun k =>
      if hk : k.1 ∈ a.fields then a.at ⟨k.1, hk⟩
      else b.at ⟨k.1, (Finset.mem_disjUnion.mp k.2).resolve_left hk⟩)
    r

@[simp] theorem Body.merge_fields (a b : Body) (h : Disjoint a.fields b.fields) {r : Rest}
    (hr : Rest.merge a.rest b.rest = some r) :
    (Body.merge a b h hr).fields = a.fields.disjUnion b.fields h := rfl

@[simp] theorem Body.merge_rest (a b : Body) (h : Disjoint a.fields b.fields) {r : Rest}
    (hr : Rest.merge a.rest b.rest = some r) : (Body.merge a b h hr).rest = r := rfl

/-- Two closed policies merge to a closed one. `codec` is the only open policy and
    `Rest.merge` refuses it, so the product of two closed factors is closed. -/
theorem TypedRest.merge_closed {x y r : Rest} (hm : Rest.merge x y = some r)
    (hx : TypedRest x none) (hy : TypedRest y none) : TypedRest r none := by
  cases hx <;> cases hy <;>
    simp only [Rest.merge, Option.some.injEq] at hm <;> subst hm
  · exact .drop
  · exact .refuse
  · exact .refuse
  · exact .refuse

/-- A binding on the merged key set: the factor that declares the name gives it. -/
def bindMerge {α : Type} (a b : Finset Name) (h : Disjoint a b)
    (fa : {k // k ∈ a} → α) (fb : {k // k ∈ b} → α) : {k // k ∈ a.disjUnion b h} → α :=
  fun k =>
    if hk : k.1 ∈ a then fa ⟨k.1, hk⟩
    else fb ⟨k.1, (Finset.mem_disjUnion.mp k.2).resolve_left hk⟩

/-- **The product of two closed objects is the object of their merged body.**

    Stated on the premises `(object)` consumes rather than on two `Typed` judgements, because
    that is the form the rule takes and inverting it back would add nothing. The held set is
    `HObject` at the merged table, which is what makes the distribution laws above this one
    statements about `HObject` and not about a second construction. -/
theorem typed_merge {a b : Body} (h : Disjoint a.fields b.fields) {r : Rest}
    (hr : Rest.merge a.rest b.rest = some r)
    {binda : {k // k ∈ a.fields} → Bool × Held} {μa : {k // k ∈ a.fields} → Option Member}
    {bindb : {k // k ∈ b.fields} → Bool × Held} {μb : {k // k ∈ b.fields} → Option Member}
    (hfa : ∀ k, TypedField (a.at k) (binda k).2 (binda k).1 (μa k))
    (hfb : ∀ k, TypedField (b.at k) (bindb k).2 (bindb k).1 (μb k))
    (hra : TypedRest a.rest none) (hrb : TypedRest b.rest none) :
    Typed (.object (Body.merge a b h hr))
      (HObject (Body.merge a b h hr).fields
        (bindMerge a.fields b.fields h binda bindb) none) (some .M) := by
  refine Typed.object (μs := bindMerge a.fields b.fields h μa μb) ?_ ?_
  · intro k
    simp only [Body.merge, Body.at, bindMerge]
    split
    · exact hfa _
    · exact hfb _
  · exact TypedRest.merge_closed hr hra hrb

/-! ## The product law

`HObject` at the merged table, read as a statement about the two factors. The direction
`typed_merge`'s consumers need is the **forward** one: a value the product holds is a value
each factor holds on its own share of the names. -/

/-- **The forward half of the product law**: a map the product holds carries every required
    name of each factor, and holds each name that factor declares at that factor's binding.

    Stated as the four facts a distribution proof consumes rather than as a reconstruction of
    the factors' `HObject`. Rebuilding the two halves as maps is the reverse direction; it
    needs `MapOf` restriction and its extensionality, and it is not proved here. -/
theorem hobject_merge_forward {a b : Body} (h : Disjoint a.fields b.fields)
    {binda : {k // k ∈ a.fields} → Bool × Held} {bindb : {k // k ∈ b.fields} → Bool × Held}
    {keys : Finset Name} {f : {k // k ∈ keys} → Value}
    (hv : HObject (a.fields.disjUnion b.fields h)
            (bindMerge a.fields b.fields h binda bindb) none (.map keys f)) :
    (∀ k : {k // k ∈ a.fields}, (binda k).1 = true → k.1 ∈ keys) ∧
    (∀ k : {k // k ∈ b.fields}, (bindb k).1 = true → k.1 ∈ keys) ∧
    (∀ (k : {k // k ∈ a.fields}) (hk : k.1 ∈ keys), (binda k).2 (f ⟨k.1, hk⟩)) ∧
    (∀ (k : {k // k ∈ b.fields}) (hk : k.1 ∈ keys), (bindb k).2 (f ⟨k.1, hk⟩)) := by
  obtain ⟨keys', f', heq, hreq, hheld⟩ := hv
  cases heq
  have hnb : ∀ k : {k // k ∈ b.fields}, k.1 ∉ a.fields :=
    fun k hm => (Finset.disjoint_left.mp h) hm k.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk
    refine hreq ⟨k.1, Finset.mem_disjUnion.mpr (Or.inl k.2)⟩ ?_
    simpa only [bindMerge, dif_pos k.2] using hk
  · intro k hk
    refine hreq ⟨k.1, Finset.mem_disjUnion.mpr (Or.inr k.2)⟩ ?_
    simpa only [bindMerge, dif_neg (hnb k)] using hk
  · intro k hk
    have := hheld ⟨k.1, hk⟩
    rw [dif_pos (Finset.mem_disjUnion.mpr (Or.inl k.2))] at this
    simpa only [bindMerge, dif_pos k.2] using this
  · intro k hk
    have := hheld ⟨k.1, hk⟩
    rw [dif_pos (Finset.mem_disjUnion.mpr (Or.inr k.2))] at this
    simpa only [bindMerge, dif_neg (hnb k)] using this

end Calculus
