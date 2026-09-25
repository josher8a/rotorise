import Calculus.Dynamo.Lang.Typing

/-!
# The merge of two object bodies

The founding operation of the product. A product of two closed objects is the object of
their merged body, and every distribution law above it reduces to this one merge.

Not in `Products.lean`, which is the codec traversal toolkit — `carriedCodec`, `entrywise`,
`tupleCodec` — and reaches `Prisms` rather than `Typing`. This is a syntactic operation on
`Body` with a typing corollary, so it sits with what it is about.
-/

namespace Calculus

open Alg (Body.at)

/-- Two map payloads over disjoint key sets, as one.

    `Finset.disjUnion` and not `∪`: the union's membership API goes through `Finset.image`
    and `Multiset.dedup`, which reach `Classical.choice`. `disjUnion` carries the proof and
    `Finset.mem_disjUnion` is the whole of its API. -/
def MapOf.disjUnion {α : Type} (a b : MapOf α) (h : Disjoint a.keys b.keys) : MapOf α :=
  { keys := a.keys.disjUnion b.keys h
    get := fun k =>
      if hk : k.1 ∈ a.keys then a.get ⟨k.1, hk⟩
      else b.get ⟨k.1, (Finset.mem_disjUnion.mp k.2).resolve_left hk⟩ }

/-- The body of a product: the disjoint union of the field tables, and no open block.

    **The merge of two open blocks is gone rather than refused.** It used to be a nine-cell
    table over three policies that answered on the four closed cells and refused the rest.
    One closed state replaced the three, so the four cells are one cell, and the refusal has
    nothing left to decide: an open factor holds an undeclared name through a codec of its
    own, and a product would have to hold it through both. The premise says so directly, and
    the table and its three corollaries are deleted with it. -/
def Body.merge (a b : Body) (h : Disjoint a.fields b.fields)
    (_ha : a.wild = none) (_hb : b.wild = none) : Body :=
  .mk (a.fields.disjUnion b.fields h)
    (fun k =>
      if hk : k.1 ∈ a.fields then a.at ⟨k.1, hk⟩
      else b.at ⟨k.1, (Finset.mem_disjUnion.mp k.2).resolve_left hk⟩)
    none

@[simp] theorem Body.merge_fields (a b : Body) (h : Disjoint a.fields b.fields)
    (ha : a.wild = none) (hb : b.wild = none) :
    (Body.merge a b h ha hb).fields = a.fields.disjUnion b.fields h := rfl

@[simp] theorem Body.merge_wild (a b : Body) (h : Disjoint a.fields b.fields)
    (ha : a.wild = none) (hb : b.wild = none) : (Body.merge a b h ha hb).wild = none := rfl

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
theorem typed_merge {a b : Body} (h : Disjoint a.fields b.fields)
    (ha : a.wild = none) (hb : b.wild = none)
    {binda : {k // k ∈ a.fields} → Bool × Held} {μa : {k // k ∈ a.fields} → Option Member}
    {bindb : {k // k ∈ b.fields} → Bool × Held} {μb : {k // k ∈ b.fields} → Option Member}
    (hfa : ∀ k, TypedField (a.at k) (binda k).2 (binda k).1 (μa k))
    (hfb : ∀ k, TypedField (b.at k) (bindb k).2 (bindb k).1 (μb k)) :
    Typed (.object (Body.merge a b h ha hb))
      (HObject (Body.merge a b h ha hb).fields
        (bindMerge a.fields b.fields h binda bindb) none) (some .M) := by
  refine Typed.object (μs := bindMerge a.fields b.fields h μa μb) ?_ ?_
  · intro k
    simp only [Body.merge, Body.at, bindMerge]
    split
    · exact hfa _
    · exact hfb _
  · exact TypedWild.none

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

/-! ## Restriction, and the reverse of the product law -/

/-- A map payload narrowed to the names in `s`. `Finset.filter` and not `∩`: the record already
    admits `Finset.mem_filter`, where the intersection's membership API is a new route. -/
def MapOf.restrict {α : Type} (m : MapOf α) (s : Finset Name) : MapOf α :=
  { keys := m.keys.filter (· ∈ s)
    get := fun k => m.get ⟨k.1, (Finset.mem_filter.mp k.2).1⟩ }

@[simp] theorem MapOf.restrict_keys {α : Type} (m : MapOf α) (s : Finset Name) :
    (m.restrict s).keys = m.keys.filter (· ∈ s) := rfl

/-- Restricting a disjoint union to a set that covers one side and misses the other gives that
    side back. The name sets a body declares are what `s` is at every use. -/
theorem MapOf.restrict_disjUnion_left {α : Type} (a b : MapOf α)
    (h : Disjoint a.keys b.keys) (s : Finset Name) (hs : ∀ k ∈ a.keys, k ∈ s)
    (hb : ∀ k ∈ b.keys, k ∉ s) : (a.disjUnion b h).restrict s = a := by
  refine MapOf.ext ?_ ?_
  · ext k
    simp only [MapOf.restrict_keys, MapOf.disjUnion, Finset.mem_filter,
      Finset.mem_disjUnion]
    constructor
    · rintro ⟨hk | hk, hks⟩
      · exact hk
      · exact absurd hks (hb k hk)
    · exact fun hk => ⟨Or.inl hk, hs k hk⟩
  · intro k h₁ h₂
    simp only [MapOf.restrict, MapOf.disjUnion, dif_pos h₂]

theorem MapOf.restrict_disjUnion_right {α : Type} (a b : MapOf α)
    (h : Disjoint a.keys b.keys) (s : Finset Name) (hs : ∀ k ∈ b.keys, k ∈ s)
    (ha : ∀ k ∈ a.keys, k ∉ s) : (a.disjUnion b h).restrict s = b := by
  refine MapOf.ext ?_ ?_
  · ext k
    simp only [MapOf.restrict_keys, MapOf.disjUnion, Finset.mem_filter,
      Finset.mem_disjUnion]
    constructor
    · rintro ⟨hk | hk, hks⟩
      · exact absurd hks (ha k hk)
      · exact hk
    · exact fun hk => ⟨Or.inr hk, hs k hk⟩
  · intro k h₁ h₂
    have : k ∉ a.keys := fun hm => ha k hm (hs k h₂)
    simp only [MapOf.restrict, MapOf.disjUnion, dif_neg this]

/-- A map payload as a value. -/
def MapOf.toValue (m : MapOf Value) : Value := .map m.keys m.get

/-- **The product law, both directions.**

    A map is held by the merged body exactly when its names all fall to one factor or the other
    and each factor holds the half it declares.

    **The key-coverage conjunct is not bookkeeping.** Without it the reverse is false: a name in
    neither factor is dropped by both restrictions, so both halves are held while the merged body
    is not. A closed body holds no undeclared name, and that fact has to be carried. -/
theorem hobject_merge {a b : Body} (h : Disjoint a.fields b.fields)
    {binda : {k // k ∈ a.fields} → Bool × Held} {bindb : {k // k ∈ b.fields} → Bool × Held}
    {keys : Finset Name} {f : {k // k ∈ keys} → Value} :
    HObject (a.fields.disjUnion b.fields h)
        (bindMerge a.fields b.fields h binda bindb) none (.map keys f)
    ↔ ((∀ k ∈ keys, k ∈ a.fields.disjUnion b.fields h) ∧
       HObject a.fields binda none ((MapOf.mk keys f).restrict a.fields).toValue ∧
       HObject b.fields bindb none ((MapOf.mk keys f).restrict b.fields).toValue) := by
  have hnb : ∀ k : {k // k ∈ b.fields}, k.1 ∉ a.fields :=
    fun k hm => (Finset.disjoint_left.mp h) hm k.2
  constructor
  · rintro ⟨keys', f', heq, hreq, hheld⟩
    cases heq
    have hcov : ∀ k, k ∈ keys → k ∈ a.fields.disjUnion b.fields h := by
      intro k hk
      have hx := hheld ⟨k, hk⟩
      split at hx
      · assumption
      · obtain ⟨_, hT, _⟩ := hx; exact absurd hT (by simp)
    refine ⟨hcov, ⟨_, _, rfl, ?_, ?_⟩, ⟨_, _, rfl, ?_, ?_⟩⟩
    · intro k hk
      simp only [MapOf.restrict_keys, Finset.mem_filter]
      refine ⟨hreq ⟨k.1, Finset.mem_disjUnion.mpr (Or.inl k.2)⟩ ?_, k.2⟩
      simpa only [bindMerge, dif_pos k.2] using hk
    · intro k
      have hka : k.1 ∈ a.fields := (Finset.mem_filter.mp k.2).2
      have hx := hheld ⟨k.1, (Finset.mem_filter.mp k.2).1⟩
      rw [dif_pos (Finset.mem_disjUnion.mpr (Or.inl hka))] at hx
      rw [dif_pos hka]
      simpa only [MapOf.restrict, MapOf.toValue, bindMerge, dif_pos hka] using hx
    · intro k hk
      simp only [MapOf.restrict_keys, Finset.mem_filter]
      refine ⟨hreq ⟨k.1, Finset.mem_disjUnion.mpr (Or.inr k.2)⟩ ?_, k.2⟩
      simpa only [bindMerge, dif_neg (hnb k)] using hk
    · intro k
      have hkb : k.1 ∈ b.fields := (Finset.mem_filter.mp k.2).2
      have hx := hheld ⟨k.1, (Finset.mem_filter.mp k.2).1⟩
      rw [dif_pos (Finset.mem_disjUnion.mpr (Or.inr hkb))] at hx
      rw [dif_pos hkb]
      simpa only [MapOf.restrict, MapOf.toValue, bindMerge,
        dif_neg (hnb ⟨k.1, hkb⟩)] using hx
  · rintro ⟨hcov, ⟨_, _, heqa, hreqa, hhelda⟩, ⟨_, _, heqb, hreqb, hheldb⟩⟩
    cases heqa; cases heqb
    refine ⟨keys, f, rfl, ?_, ?_⟩
    · intro k hk
      rcases Finset.mem_disjUnion.mp k.2 with hka | hkb
      · have := hreqa ⟨k.1, hka⟩ (by simpa only [bindMerge, dif_pos hka] using hk)
        exact (Finset.mem_filter.mp this).1
      · have := hreqb ⟨k.1, hkb⟩
          (by simpa only [bindMerge, dif_neg (hnb ⟨k.1, hkb⟩)] using hk)
        exact (Finset.mem_filter.mp this).1
    · intro k
      rw [dif_pos (hcov k.1 k.2)]
      rcases Finset.mem_disjUnion.mp (hcov k.1 k.2) with hka | hkb
      · have := hhelda ⟨k.1, Finset.mem_filter.mpr ⟨k.2, hka⟩⟩
        rw [dif_pos hka] at this
        simpa only [bindMerge, dif_pos hka, MapOf.restrict, MapOf.toValue] using this
      · have := hheldb ⟨k.1, Finset.mem_filter.mpr ⟨k.2, hkb⟩⟩
        rw [dif_pos hkb] at this
        simpa only [bindMerge, dif_neg (hnb ⟨k.1, hkb⟩), MapOf.restrict,
          MapOf.toValue] using this

/-! ## Distribution

The product of a held set with another, on disjoint name sets. `hobject_merge` says the merged
body's held set is exactly this, so a distribution law is a statement about `HProdOn` and not
about a second construction. -/

/-- The product of two held sets over disjoint name sets, as `hobject_merge` reads it. -/
def HProdOn (na nb : Finset Name) (Ta Tb : Held) : Held :=
  fun v => ∃ keys f, v = .map keys f ∧ (∀ k ∈ keys, k ∈ na ∨ k ∈ nb) ∧
    Ta ((MapOf.mk keys f).restrict na).toValue ∧
    Tb ((MapOf.mk keys f).restrict nb).toValue

/-- **Incomparability survives a product, and it needs the other factor inhabited.**

    The witness that separates `Ta` from `Ta'` extends by any `Tb`-held half to a witness that
    separates the two products: the extension restricts back to the original on `na`, so `Ta'`
    fails there for the reason it failed before.

    **`hb` is not bookkeeping.** A factor that holds nothing makes every product hold nothing, and
    two empty held sets are comparable in both directions, so incomparability fails at the product
    however well the factors separate. -/
theorem not_subset_prodOn {na nb : Finset Name} (h : Disjoint na nb) {Ta Ta' Tb : Held}
    {ka : Finset Name} {fa : {k // k ∈ ka} → Value} (hka : ∀ k ∈ ka, k ∈ na)
    (hv : Ta (.map ka fa)) (hv' : ¬ Ta' (.map ka fa))
    {kb : Finset Name} {fb : {k // k ∈ kb} → Value} (hkb : ∀ k ∈ kb, k ∈ nb)
    (hb : Tb (.map kb fb)) :
    ¬ (∀ v, HProdOn na nb Ta Tb v → HProdOn na nb Ta' Tb v) := by
  have hdis : Disjoint ka kb :=
    Finset.disjoint_left.mpr fun k hk hk' =>
      (Finset.disjoint_left.mp h) (hka k hk) (hkb k hk')
  have hbna : ∀ k ∈ kb, k ∉ na := fun k hk hm =>
    (Finset.disjoint_left.mp h) hm (hkb k hk)
  have hanb : ∀ k ∈ ka, k ∉ nb := fun k hk hm =>
    (Finset.disjoint_left.mp h) (hka k hk) hm
  set m := (MapOf.mk ka fa).disjUnion (MapOf.mk kb fb) hdis with hm
  have hla : m.restrict na = MapOf.mk ka fa :=
    MapOf.restrict_disjUnion_left _ _ hdis na hka hbna
  have hlb : m.restrict nb = MapOf.mk kb fb :=
    MapOf.restrict_disjUnion_right _ _ hdis nb hkb hanb
  intro hsub
  have hin : HProdOn na nb Ta Tb m.toValue := by
    refine ⟨m.keys, m.get, rfl, ?_, ?_, ?_⟩
    · intro k hk
      have hk' : k ∈ ka.disjUnion kb hdis := hk
      rcases Finset.mem_disjUnion.mp hk' with hk'' | hk''
      · exact Or.inl (hka k hk'')
      · exact Or.inr (hkb k hk'')
    · rw [show (MapOf.mk m.keys m.get) = m from rfl, hla]; exact hv
    · rw [show (MapOf.mk m.keys m.get) = m from rfl, hlb]; exact hb
  obtain ⟨keys', f', heq, _, hTa', _⟩ := hsub _ hin
  rw [show m.toValue = .map m.keys m.get from rfl] at heq
  cases heq
  rw [show (MapOf.mk m.keys m.get) = m from rfl, hla] at hTa'
  exact hv' hTa'

/-! ## Associativity -/


/-- The merged name set does not depend on the grouping. Through `Finset.ext` and
    `Finset.mem_disjUnion`, both of which the gateway record already admits. -/
theorem Body.merge_fields_assoc {a b c : Body}
    (hab : Disjoint a.fields b.fields) (hbc : Disjoint b.fields c.fields)
    (hl : Disjoint (a.fields.disjUnion b.fields hab) c.fields)
    (hr : Disjoint a.fields (b.fields.disjUnion c.fields hbc)) :
    (a.fields.disjUnion b.fields hab).disjUnion c.fields hl
      = a.fields.disjUnion (b.fields.disjUnion c.fields hbc) hr := by
  ext k
  simp only [Finset.mem_disjUnion]
  exact or_assoc

end Calculus
