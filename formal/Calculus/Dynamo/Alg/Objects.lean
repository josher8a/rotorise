import Calculus.Dynamo.Alg.Products

/-!
# Objects

The field table is a map rather than a row, and the object is taken apart through it.
`objectCodec` is not argued on its own: `objectCodecCore_eq` cashes it as an equation.
-/

namespace Calculus

section
/-! ## Objects -/

/-- A field, denoted, at the DynamoDB carriers. -/
abbrev FieldSem := Alg.FieldSem Value Member

/-- A rest policy, denoted, at the DynamoDB carriers. -/
abbrev RestSem := Alg.RestSem Value Member

/- The fields, a slot's behavior at absence and the rest codec take the carriers as parameters.
   The aliases give them their names in this namespace. `FieldSem.codec` has no alias, because an
   alias captures field notation, and field notation reaches the generic name through the
   abbreviation. -/
export Alg (absentOf rcOf)

namespace FieldSem
export Alg.FieldSem (Rel)
end FieldSem

namespace RestSem
export Alg.RestSem (Rel)
end RestSem

/-! ### The field table is a map, not a row

An object declares a *set* of field names, each with one field, so the table is a `MapOf`, exactly as
`M`'s payload is, and for the same reason. The slots, the entry codec and the payload map read no
carrier constructor, so they are the generic layer's (`Alg.objAt` and its neighbours), and the
aliases below give them their names in this namespace. -/

export Alg (objEntryT slotT entryCodec liftTable objAt objAt_eq objAt_at)

section Object
variable {sems : MapOf FieldSem} {rc? : Option Codec}

/-- The object is `carriedCodec` at the `M` prism: the generic object at that prism. -/
abbrev objectCodecCore (sems : MapOf FieldSem) (rc? : Option Codec) : Codec :=
  Alg.objectCodecCore mS sems rc?

/-- The `object`, at the `M` prism. -/
abbrev objectCodec (sems : MapOf FieldSem) (rest : RestSem) : Codec :=
  Alg.objectCodec mS sems rest

theorem objectCodecCore_eq :
    objectCodecCore sems rc? =
      carriedCodec mS
        (fun p => ∀ k, slotT sems rc? k (p.at k)) (objAt sems rc?) := rfl

/-- **The rule `(record)`: the object that declares no name and takes every key at one codec.** It is
    not a construct of its own: `Term.record` is the empty body with an open block, and its
    codec is the object codec of that body. -/
abbrev recordCodec (c : Codec) : Codec :=
  objectCodec ⟨∅, fun k => absurd k.2 (Finset.notMem_empty k.1)⟩ (.codec c)

/-- The empty body declares no name. -/
theorem emptyBody_at (k : Name) :
    (⟨∅, fun k => absurd k.2 (Finset.notMem_empty k.1)⟩ : MapOf FieldSem).at k = none :=
  MapOf.at_none (Finset.notMem_empty k)

/-- **A record moves entry by entry**, at each orientation: the same name set, every entry
    through `c`. -/
theorem recordCodec_f (o : Alg.Orient) (c : Codec) (keys : Finset Name)
    (g : {k // k ∈ keys} → Attr) :
    (recordCodec c).f o (.m keys g) = (funImage fun k => c.f o (g k)).map (Attr.m keys) := by
  have hent : ∀ k, entryCodec (⟨∅, fun k => absurd k.2 (Finset.notMem_empty k.1)⟩ :
      MapOf FieldSem) (some c) k = some c := fun k => by simp only [entryCodec, emptyBody_at]
  have hlift : ∀ k (hk : k ∈ keys), liftTable ⟨∅, fun k => absurd k.2 (Finset.notMem_empty k.1)⟩
      (some c) k o ((⟨keys, g⟩ : MapOf Attr).at k) = (c.f o (g ⟨k, hk⟩)).map some := fun k hk => by
    rw [MapOf.at_of_mem (m := ⟨keys, g⟩) ⟨k, hk⟩]
    simp only [liftTable, hent, Option.bind_some]
  have hmem : ∀ k, k ∈ (∅ : Finset Name) ∪ keys ↔ k ∈ keys := fun k =>
    ⟨fun h => (Finset.mem_union.mp h).resolve_left (Finset.notMem_empty k),
      fun h => Finset.mem_union.mpr (Or.inr h)⟩
  simp only [carriedCodec, Option.bind, rcOf, mS, mA]
  rcases hf : funImage (fun k => c.f o (g k)) with _ | h
  · refine Option.map_eq_none_iff.mpr (Option.not_isSome_iff_eq_none.mp fun hs => ?_)
    have hall : ∀ k : {k // k ∈ keys}, (c.f o (g k)).isSome = true := fun k => by
      have h1 := (Alg.objP_eq (q := (objAt _ (some c) o ⟨keys, g⟩).get hs)).mp
        (Option.some_get hs).symm |>.1 k.1 ((hmem k.1).mpr k.2)
      rw [hlift k.1 k.2] at h1
      rw [← Option.isSome_map (f := some), h1]; rfl
    have := funImage_isSome hall
    rw [hf] at this
    exact nomatch this
  · have hg := funImage_some hf
    have hq : objAt (⟨∅, fun k => absurd k.2 (Finset.notMem_empty k.1)⟩ : MapOf FieldSem)
        (some c) o ⟨keys, g⟩ = some ⟨keys, h⟩ := by
      refine Alg.objP_eq.mpr ⟨fun k hk => ?_, fun k hk => (hmem k).mpr hk⟩
      have hk := (hmem k).mp hk
      rw [hlift k hk, hg ⟨k, hk⟩, MapOf.at_of_mem (m := ⟨keys, h⟩) ⟨k, hk⟩]
      rfl
    rw [hq]
    rfl

/-- **A record holds a map whose every entry the codec holds.** -/
theorem recordCodec_T (c : Codec) (keys : Finset Name) (g : {k // k ∈ keys} → Attr) :
    (recordCodec c).T (.m keys g) ↔ ∀ k, c.T (g k) := by
  constructor
  · rintro ⟨⟨xk, xg⟩, hx, h⟩ k
    simp only [mS, mA] at hx; cases hx
    have := h k.1
    simp only [Alg.slotT, MapOf.at_of_mem (m := ⟨keys, g⟩) k, objEntryT, rcOf, emptyBody_at] at this
    obtain ⟨_, ⟨⟩, h⟩ := this
    exact h
  · intro h
    refine ⟨⟨keys, g⟩, rfl, fun k => ?_⟩
    rcases Decidable.em (k ∈ keys) with hk | hk
    · simp only [MapOf.at_of_mem (m := ⟨keys, g⟩) ⟨k, hk⟩, Alg.slotT, objEntryT, rcOf, emptyBody_at]
      exact ⟨c, rfl, h ⟨k, hk⟩⟩
    · simp only [MapOf.at_none (m := ⟨keys, g⟩) hk, Alg.slotT, absentOf, emptyBody_at,
        Option.isSome_some]

end Object

end

end Calculus
