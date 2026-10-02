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

/- The fields, the guards and the rest codec take the carriers as parameters. The aliases give
   them their names in this namespace. `FieldSem.codec` has no alias, because an alias captures
   field notation, and field notation reaches the generic name through the abbreviation. -/
export Alg (valPresentAt rcOf)

namespace FieldSem
export Alg.FieldSem (Rel)
end FieldSem

namespace RestSem
export Alg.RestSem (Rel)
end RestSem

/-! ### The field table is a map, not a row

§4 declares a *set* of field names, each with one field, so the table is a `MapOf`, exactly as
`M`'s payload is, and for the same reason. The guards, the filter, the entry codec and the payload
map read no carrier constructor, so they are the generic layer's (`Alg.objAt` and its
neighbours), and the aliases below give them their names in this namespace. -/

export Alg (valPresentB objEntryT entryCodec objAt objAt_eq)

section Object
variable {sems : MapOf FieldSem} {rc? : Option Codec}

/-- The object is `carriedCodec` at the `M` prism: the generic object at that prism. -/
noncomputable abbrev objectCodecCore (sems : MapOf FieldSem) (rc? : Option Codec) : Codec :=
  Alg.objectCodecCore mA .M sems rc?

/-- §4's `object`, at the `M` prism. -/
noncomputable abbrev objectCodec (sems : MapOf FieldSem) (rest : RestSem) : Codec :=
  Alg.objectCodec mA .M sems rest

theorem objectCodecCore_eq :
    objectCodecCore sems rc? =
      carriedCodec mA .M
        (fun p => valPresentB sems p.1 = true ∧ ∀ k, objEntryT sems rc? (k.1, p.2 k))
        (objAt sems rc?) := rfl

/-- **§3 `record`: the object that declares no name and takes every key at one codec.** It is
    not a construct of its own: `Term.record` is the empty body with an open block, and its
    codec is the object codec of that body. -/
noncomputable abbrev recordCodec (c : Codec) : Codec :=
  objectCodec ⟨∅, fun k => absurd k.2 (Finset.notMem_empty k.1)⟩ (.codec c)

/-- The empty body requires no name. A direct term: `simp` over a vacuous `Finset ∅` reaches
    `Classical.choice` through filter lemmas that this development does not advertise. -/
theorem valPresentB_empty (keys : Finset Name) :
    valPresentB (⟨∅, fun k => absurd k.2 (Finset.notMem_empty k.1)⟩ : MapOf FieldSem) keys =
      true :=
  decide_eq_true (fun k => absurd k.2 (Finset.notMem_empty k.1))

/-- **A record moves entry by entry**, at each orientation: the same name set, every entry
    through `c`. -/
theorem recordCodec_f (o : Alg.Orient) (c : Codec) (keys : Finset Name)
    (g : {k // k ∈ keys} → Attr) :
    (recordCodec c).f o (.m keys g) = (funImage fun k => c.f o (g k)).map (Attr.m keys) := by
  simp only [objectCodec, Alg.objectCodec, Alg.objectCodecCore, carriedCodec, Option.bind,
    objAt, rcOf, entryCodec, MapOf.at, mA]
  rw [if_pos (valPresentB_empty keys), Option.map_map]
  refine congrArg (fun F => Option.map F _) (funext fun _ => rfl) |>.trans ?_
  exact congrArg (Option.map _) (congrArg funImage
    (funext fun k => by rw [dif_neg (Finset.notMem_empty k.1)]))

/-- **A record holds a map whose every entry the codec holds.** -/
theorem recordCodec_T (c : Codec) (keys : Finset Name) (g : {k // k ∈ keys} → Attr) :
    (recordCodec c).T (.m keys g) ↔ ∀ k, c.T (g k) := by
  constructor
  · rintro ⟨x, hx, -, h⟩ k
    simp only [mA] at hx; cases hx
    have := h k
    simp only [objEntryT, rcOf, MapOf.at, dif_neg (Finset.notMem_empty k.1)] at this
    obtain ⟨_, ⟨⟩, h⟩ := this
    exact h
  · intro h
    refine ⟨⟨keys, g⟩, rfl, valPresentB_empty keys, fun k => ?_⟩
    simp only [objEntryT, rcOf, MapOf.at, dif_neg (Finset.notMem_empty k.1)]
    exact ⟨c, rfl, h k⟩

end Object

end

end Calculus
