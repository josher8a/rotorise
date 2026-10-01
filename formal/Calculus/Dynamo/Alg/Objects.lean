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
pair read no carrier constructor, so they are the generic layer's (`Alg.objWrite` and its
neighbours), and the aliases below give them their names in this namespace. -/

export Alg (valPresentB objEntryT entryCodec objAt objWrite objRead objAt_eq)

section Object
variable {sems : MapOf FieldSem} {rc? : Option Codec}

/-- The object is `carriedCodec` at the `M` prism: the generic object at that prism. -/
noncomputable abbrev objectCodecCore (sems : MapOf FieldSem) (rc? : Option Codec) : Codec :=
  Alg.objectCodecCore mA mA .M sems rc?

/-- §4's `object`, at the `M` prism. -/
noncomputable abbrev objectCodec (sems : MapOf FieldSem) (rest : RestSem) : Codec :=
  Alg.objectCodec mA mA .M sems rest

theorem objectCodecCore_eq :
    objectCodecCore sems rc? =
      carriedCodec mA mA .M
        (fun p => valPresentB sems p.1 = true ∧ ∀ k, objEntryT sems rc? (k.1, p.2 k))
        (objWrite sems rc?) (objRead sems rc?) := rfl

/-- **The empty body with an open block is the record.** `record` is not a term of its own: it
    is the object that declares no name and takes every key at one codec, and this is the
    equation that says so. -/
theorem objectCodec_empty_codec (c : Codec) :
    objectCodec ⟨∅, fun k => absurd k.2 (Finset.notMem_empty k.1)⟩ (.codec c) = recordCodec c := by
  -- A quantifier over the empty key set is vacuous, and simp discharges one through an
  -- emptiness instance that reaches `Classical.choice`. `hval` is the same fact as a direct
  -- term, so the guard rewrites without the instance and the route stays closed.
  have hval : ∀ keys : Finset Name,
      valPresentB (⟨∅, fun k => absurd k.2 (Finset.notMem_empty k.1)⟩ : MapOf FieldSem) keys
        = true :=
    fun _ => decide_eq_true (fun k => absurd k.2 (Finset.notMem_empty k.1))
  apply Codec.ext
  · funext v
    cases v <;>
      simp [objectCodec, Alg.objectCodec, Alg.objectCodecCore, carriedCodec, recordCodec, objEntryT, rcOf, MapOf.at, mA]
    constructor
    · rintro ⟨x, ⟨rfl, hf⟩, h⟩
      cases eq_of_heq hf
      exact h.2
    · rename_i keys f
      exact fun h => ⟨⟨keys, f⟩, ⟨rfl, HEq.rfl⟩, hval keys, h⟩
  · rfl
  · funext v
    cases v <;> try rfl
    rename_i keys f
    simp only [objectCodec, Alg.objectCodec, Alg.objectCodecCore, carriedCodec, recordCodec, Option.bind, objWrite, objAt, rcOf, entryCodec, MapOf.at, mA, Alg.Codec.ofEP_e]
    rw [if_pos (hval keys), Option.map_map]
    refine congrArg (fun F => Option.map F _) (funext fun _ => rfl) |>.trans ?_
    exact congrArg (Option.map _) (congrArg funImage
      (funext fun k => by rw [dif_neg (Finset.notMem_empty k.1)]))
  · funext a
    cases a <;> try rfl
    rename_i keys f
    simp only [objectCodec, Alg.objectCodec, Alg.objectCodecCore, carriedCodec, mA, Option.bind, objRead, objAt, rcOf, entryCodec, MapOf.at, recordCodec, Alg.Codec.ofEP_p]
    -- simp over a vacuous `Finset ∅` goal reaches `Classical.choice` through three filter
    -- lemmas this development does not advertise. Each fact below is the direct term instead.
    rw [if_pos (show valPresentB (⟨(∅ : Finset Name),
        fun k => absurd k.2 (Finset.notMem_empty k.1)⟩ : MapOf FieldSem) keys = true from
      decide_eq_true (fun k => absurd k.2 (Finset.notMem_empty k.1)))]
    rw [Option.map_map]
    refine congrArg (fun F => Option.map F _) (funext fun _ => rfl) |>.trans ?_
    exact congrArg (Option.map _) (congrArg funImage
      (funext fun k => by rw [dif_neg (Finset.notMem_empty k.1)]))

end Object

end

end Calculus
