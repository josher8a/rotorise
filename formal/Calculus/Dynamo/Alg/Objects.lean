import Calculus.Dynamo.Alg.Products

/-!
# Objects (§4)

The field table is a map rather than a row, and the object is taken apart through it.
`objectCodec` is not argued on its own: `objectCodecCore_eq` cashes it as an equation.
-/

namespace Calculus

noncomputable section
/-! ## Objects (§4) -/

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

§4 declares a *set* of field names, each with one field, so the table is a `MapOf`, exactly as
`M`'s payload is, and for the same reason. The slots, the entry codec and the payload map read no
carrier constructor, so they are the generic layer's (`Alg.objAt` and its neighbours), and the
aliases below give them their names in this namespace. -/

export Alg (objEntryT slotT entryCodec liftTable objAt objAt_eq objAt_at)

section Object
variable {sems : MapOf FieldSem} {rc? : Option Codec}

/-- The object is `carriedCodec` at the `M` prism: the generic object at that prism. -/
noncomputable abbrev objectCodecCore (sems : MapOf FieldSem) (rc? : Option Codec) : Codec :=
  Alg.objectCodecCore mS sems rc?

/-- §4's `object`, at the `M` prism. -/
noncomputable abbrev objectCodec (sems : MapOf FieldSem) (rest : RestSem) : Codec :=
  Alg.objectCodec mS sems rest

theorem objectCodecCore_eq :
    objectCodecCore sems rc? =
      carriedCodec mS
        (fun p => ∀ k, slotT sems rc? k (p.at k)) (objAt sems rc?) := rfl

/-- **§3 `record`: the object that declares no name and takes every key at one codec.** It is
    not a construct of its own: `Term.record` is the empty body with an open block, and its
    codec is the object codec of that body. -/
noncomputable abbrev recordCodec (c : Codec) : Codec :=
  objectCodec ⟨∅, fun k => absurd k.2 (Finset.notMem_empty k.1)⟩ (.codec c)

/-- The empty body declares no name. -/
theorem emptyBody_at (k : Name) :
    (⟨∅, fun k => absurd k.2 (Finset.notMem_empty k.1)⟩ : MapOf FieldSem).at k = none :=
  MapOf.at_none (Finset.notMem_empty k)

/-- The empty body holds no fill. -/
theorem emptyBody_noFill :
    Alg.noFill (⟨∅, fun k => absurd k.2 (Finset.notMem_empty k.1)⟩ : MapOf FieldSem) = true :=
  decide_eq_true fun k => absurd k.2 (Finset.notMem_empty k.1)

/-- **A record moves entry by entry**, at each orientation: the same name set, every entry
    through `c`. -/
theorem recordCodec_f (o : Alg.Orient) (c : Codec) (keys : Finset Name)
    (g : {k // k ∈ keys} → Attr) :
    (recordCodec c).f o (.m keys g) = (funImage fun k => c.f o (g k)).map (Attr.m keys) := by
  simp only [carriedCodec, Option.bind, objAt, rcOf, entryCodec, mS, mA]
  rw [if_pos emptyBody_noFill, if_pos (fun k hk => absurd hk (Finset.notMem_empty k)), Option.map_map]
  refine congrArg (fun F => Option.map F _) (funext fun _ => rfl) |>.trans ?_
  exact congrArg (Option.map _) (congrArg funImage
    (funext fun k => by rw [emptyBody_at]))

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
