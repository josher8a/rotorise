import Calculus.Carriers

/-!
# Lawfulness — proved

The combinators whose laws this development discharges, argued once per construction
rather than once per term.
-/

namespace Calculus

noncomputable section
/-! ## Lawfulness — proved -/

/-! ### The point ground codecs, argued once

`string`, `boolean`, `binary` and `null` are `pointCodec` at four different pairs of
prisms. Below, each of the four is that one lemma transported across the definitional
equality by `Lawful.congr`, which is what lets the definitions stay in the unfolded form
the rest of the development `simp`s with. -/

/-- §2's laws for any pair of prisms. The one premise a prism pair does not already supply is
    which member the attribute side stamps. Everything else is `out_into` and `into_out`. -/
theorem lawful_pointCodec {α : Type} {V : Ctor α Value} {A : Ctor α Attr} {μ₀ : Member}
    (hμ : ∀ x, (A.into x).member = μ₀) :
    Lawful (pointCodec V A μ₀) := by
  refine ⟨?_, ?_, ?_⟩
  · -- (R): match, rebuild, match again — `out_into` on each side.
    intro t a he
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp he
    simp [pointCodec, A.out_into, ← V.into_out hx]
  · -- (C): what `p` produced was built by `V`, and `A` rebuilds the attribute it read.
    intro a t hp
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hp
    simp [pointCodec, V.out_into, A.into_out hx]
  · -- (W): everything written is `A.into` of something.
    intro μ hm t a he
    obtain ⟨x, _, rfl⟩ := Option.map_eq_some_iff.mp he
    cases hm; exact hμ x

theorem lawful_stringCodec : Lawful stringCodec :=
  Lawful.congr (d := pointCodec strV sC .S)
    (by funext v; cases v <;> rfl) (by funext a; cases a <;> rfl) rfl
    (lawful_pointCodec (fun _ => rfl))

theorem lawful_booleanCodec : Lawful booleanCodec :=
  Lawful.congr (d := pointCodec boolV boolA .BOOL)
    (by funext v; cases v <;> rfl) (by funext a; cases a <;> rfl) rfl
    (lawful_pointCodec (fun _ => rfl))

theorem lawful_binaryCodec : Lawful binaryCodec :=
  Lawful.congr (d := pointCodec binV bC .B)
    (by funext v; cases v <;> rfl) (by funext a; cases a <;> rfl) rfl
    (lawful_pointCodec (fun _ => rfl))

theorem lawful_nullCodec : Lawful nullCodec :=
  Lawful.congr (d := pointCodec nullV nullA .NULL)
    (by funext v; cases v <;> rfl) (by funext a; cases a <;> rfl) rfl
    (lawful_pointCodec (fun _ => rfl))

/-- **The `(number)` case, with no axiom.** `e` and `p` are mutually inverse constructor
    wrappers over one carrier, so retract, canon and writes are `rfl` at the only inhabited
    row. No shortest-text round trip is needed, because there is no host spelling to
    round-trip through. -/
theorem lawful_numberCodec : Lawful numberCodec := by
  refine ⟨?_, ?_, ?_⟩
  · intro t a he
    cases t with
    | num x => cases he; rfl
    | _ => exact nomatch he
  · intro a t hp
    cases a with
    | n x => cases hp; rfl
    | _ => exact nomatch hp
  · intro μ hμ t a he
    cases t with
    | num x => cases he; cases hμ; rfl
    | _ => exact nomatch he

theorem LawfulCore.through {c : Codec} (h : LawfulCore c) {f g : Value → Value}
    (hiso : IsoCancels c f g) :
    LawfulCore (c.through f g) where
  retract he := through_p.mpr ⟨_, h.retract (through_e.mp he),
    (hiso.1 _ (by rw [through_e.mp he]; rfl)).symm⟩
  canon hp := by
    obtain ⟨w, hw, rfl⟩ := through_p.mp hp
    show (c.e (f (g w))).isSome
    rw [hiso.2 w (h.canon hw)]
    exact h.canon hw
  writes := by intro μ hμ t a he; exact h.writes hμ (through_e.mp he)

/-- `held` preserves the laws: the core lemma, plus canonical reads through the iso. -/
theorem Lawful.through {c : Codec} (h : Lawful c) {f g : Value → Value}
    (hiso : IsoCancels c f g) :
    Lawful (c.through f g) :=
  { LawfulCore.through h.core hiso with
    canon := by
      intro a t hp
      obtain ⟨w, hw, rfl⟩ := through_p.mp hp
      rw [through_e, hiso.2 w (h.defined hw)]; exact h.canon hw }

/-- `refine` preserves the laws: everything restricts. -/
theorem LawfulCore.restrict {c : Codec} (h : LawfulCore c) (q : Value → Bool) :
    LawfulCore (c.restrict q) where
  retract he :=
    let ⟨hq, hc⟩ := restrict_e.mp he
    restrict_p.mpr ⟨h.retract hc, hq⟩
  canon hp :=
    let ⟨hc, hq⟩ := restrict_p.mp hp
    Option.isSome_iff_exists.mpr
      (let ⟨a, ha⟩ := Option.isSome_iff_exists.mp (h.canon hc)
       ⟨a, restrict_e.mpr ⟨hq, ha⟩⟩)
  writes := by intro μ hμ t a he; exact h.writes hμ (restrict_e.mp he).2

theorem Lawful.restrict {c : Codec} (h : Lawful c) (q : Value → Bool) :
    Lawful (c.restrict q) :=
  { LawfulCore.restrict h.core q with
    canon := fun hp => let ⟨hc, hq⟩ := restrict_p.mp hp; restrict_e.mpr ⟨hq, h.canon hc⟩ }


/-- …and every base is lawful. -/
theorem lawful_baseCodec : ∀ k : GroundKind, Lawful (baseCodec k)
  | .string  => lawful_stringCodec
  | .number  => lawful_numberCodec
  | .boolean => lawful_booleanCodec
  | .binary  => lawful_binaryCodec
  | .null    => lawful_nullCodec

/-! ### The literal codec is lawful because its base is

`literal` adds a prism and nothing else, so retract, canon and writes come from
`Lawful.restrict`. That is one statement, because there is one codec. -/

/-- §3 `(literal)` is lawful, full stop.

    **No `ℓ ⊆ D` hypothesis, and the proof never needed one.** `Lawful` relates `e` and `p` to
    each other and never mentions `T`, so a restriction of a lawful pair is lawful whether or
    not the restriction is inhabited. That is why §3's `ℓ ⊆ D` belongs to the carrier and not
    here. -/
theorem lawful_literalCodec (k : GroundKind) (x : k.Carrier) :
    Lawful (literalCodec k x) :=
  Lawful.congr (d := (baseCodec k).restrict (inL k x)) rfl rfl rfl
    (Lawful.restrict (lawful_baseCodec k) (inL k x))

theorem LawfulCore.extendRead {c : Codec} (h : LawfulCore c) {r : Attr → Option Value}
    (hran : ∀ a v, r a = some v → (c.e v).isSome) :
    LawfulCore (c.extendRead r) where
  retract he := extendRead_p.mpr (.inl (h.retract (extendRead_e.mp he)))
  canon hp := (extendRead_p.mp hp).elim h.canon fun ⟨_, hr⟩ => hran _ _ hr
  writes := by intro μ hμ t a he; exact h.writes hμ (extendRead_e.mp he)

end

end Calculus
