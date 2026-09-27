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
abbrev FieldSem := Alg.FieldSem Value Attr Member

/-- A rest policy, denoted, at the DynamoDB carriers. -/
abbrev RestSem := Alg.RestSem Value Attr Member

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

export Alg (valPresentB reqPresentB keepB objEntryT entryCodec objWrite objRead objWrite_eq)

section Object
variable {sems : MapOf FieldSem} {rc? : Option Codec} {kn : Name → Bool}

/-- A filter that keeps every name transports an entrywise read to a record read. -/
theorem funImage_record_congr {S T : Finset Name} (hS : S = T)
    {g : {k // k ∈ S} → Option Value} {g' : {k // k ∈ T} → Option Value}
    (hg : ∀ (k : Name) (h : k ∈ S) (h' : k ∈ T), g ⟨k, h⟩ = g' ⟨k, h'⟩) :
    (funImage g).map (Value.map S) = (funImage g').map (Value.map T) := by
  subst hS
  have himg : g = g' := funext fun k => hg k.1 k.2 k.2
  subst himg
  rfl

/-- The object is `carriedCodec` between `map` and `M`, at that pair: the generic object at the
    `map` and `M` prisms. -/
noncomputable abbrev objectCodecCore (sems : MapOf FieldSem) (rc? : Option Codec)
    (kn : Name → Bool) : Codec :=
  Alg.objectCodecCore mapV mA .M sems rc? kn

/-- §4's `object`, at the `map` and `M` prisms. -/
noncomputable abbrev objectCodec (sems : MapOf FieldSem) (rest : RestSem) : Codec :=
  Alg.objectCodec mapV mA .M sems rest

theorem objectCodecCore_eq :
    objectCodecCore sems rc? kn =
      carriedCodec mapV mA .M
        (fun p => valPresentB sems p.1 = true ∧ ∀ k, objEntryT sems rc? (k.1, p.2 k))
        (objWrite sems rc?) (objRead sems rc? kn) := rfl

/-- **The empty body with an open block is the record.** `record` is not a term of its own: it
    is the object that declares no name and takes every key at one codec, and this is the
    equation that says so. Four components, and only the reading needs work: the keep filter is
    constantly true at an open block, so it drops no name. The output key set is therefore the
    map's own. `funImage_record_congr` carries the filter as a variable, which keeps the
    transport out of a dependent rewrite. -/
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
      simp [objectCodec, Alg.objectCodec, Alg.objectCodecCore, carriedCodec, recordCodec,
            objEntryT, rcOf, MapOf.at, mapV]
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
    simp only [objectCodec, Alg.objectCodec, Alg.objectCodecCore, carriedCodec, recordCodec,
        Option.bind,
          objWrite, rcOf, entryCodec, MapOf.at, mapV, mA]
    rw [if_pos (hval keys), Option.map_map]
    refine congrArg (fun F => Option.map F _) (funext fun _ => rfl) |>.trans ?_
    exact congrArg (Option.map _) (congrArg funImage
      (funext fun k => by rw [dif_neg (Finset.notMem_empty k.1)]))
  · funext a
    cases a <;> try rfl
    rename_i keys f
    simp only [objectCodec, Alg.objectCodec, Alg.objectCodecCore, carriedCodec, mapV, mA,
        Option.bind,
               objRead, rcOf, recordCodec]
    -- simp over a vacuous `Finset ∅` goal reaches `Classical.choice` through three filter
    -- lemmas this development does not advertise. Each fact below is the direct term instead.
    rw [if_pos (show reqPresentB (⟨(∅ : Finset Name),
        fun k => absurd k.2 (Finset.notMem_empty k.1)⟩ : MapOf FieldSem) keys = true from
      decide_eq_true (fun k => absurd k.2 (Finset.notMem_empty k.1)))]
    have hkeep : keys.filter
        (keepB (.codec c)
          (⟨(∅ : Finset Name), fun k => absurd k.2 (Finset.notMem_empty k.1)⟩ : MapOf FieldSem) ·)
          = keys :=
      Finset.ext fun k =>
        ⟨fun hk => (Finset.mem_filter.mp hk).1, fun hk => Finset.mem_filter.mpr ⟨hk, rfl⟩⟩
    rw [Option.map_map]
    exact funImage_record_congr hkeep (fun k h h' => rfl)

end Object

end

end Calculus
