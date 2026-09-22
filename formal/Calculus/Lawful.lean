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

/-- §2's four laws for any pair of prisms. The two premises are the only things a prism
    pair does not already supply: which member the attribute side stamps, and that `≼` is
    reflexive on its image. Everything else is `out_into` and `into_out`. -/
theorem lawful_pointCodec {α : Type} {V : Ctor α Value} {A : Ctor α Attr} {μ₀ : Member}
    (hμ : ∀ x, (A.into x).member = μ₀) (hrefl : ∀ x, Agree (A.into x) (A.into x)) :
    Lawful (pointCodec V A μ₀) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (R): match, rebuild, match again — `out_into` on each side.
    intro t a he
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp he
    simp [pointCodec, A.out_into, ← V.into_out hx]
  · -- (C): what `p` produced was built by `V`, so `V.out` matches it.
    intro a t hp
    obtain ⟨x, _, rfl⟩ := Option.map_eq_some_iff.mp hp
    simp [pointCodec, V.out_into]
  · -- (W): everything written is `A.into` of something.
    intro μ hm t a he
    obtain ⟨x, _, rfl⟩ := Option.map_eq_some_iff.mp he
    cases hm; exact hμ x
  · -- (MP): the re-encoding is the attribute itself, not merely an agreeing one.
    intro a t a' hp he
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hp
    simp only [pointCodec, V.out_into, Option.map_some] at he
    cases he
    rw [A.into_out hx]
    exact hrefl x

theorem lawful_stringCodec : Lawful stringCodec :=
  Lawful.congr (d := pointCodec strV sC .S)
    (by funext v; cases v <;> rfl) (by funext a; cases a <;> rfl) rfl
    (lawful_pointCodec (fun _ => rfl) (fun _ => .s ..))

theorem lawful_booleanCodec : Lawful booleanCodec :=
  Lawful.congr (d := pointCodec boolV boolA .BOOL)
    (by funext v; cases v <;> rfl) (by funext a; cases a <;> rfl) rfl
    (lawful_pointCodec (fun _ => rfl) (fun _ => .bool ..))

theorem lawful_binaryCodec : Lawful binaryCodec :=
  Lawful.congr (d := pointCodec binV bC .B)
    (by funext v; cases v <;> rfl) (by funext a; cases a <;> rfl) rfl
    (lawful_pointCodec (fun _ => rfl) (fun _ => .b ..))

theorem lawful_nullCodec : Lawful nullCodec :=
  Lawful.congr (d := pointCodec nullV nullA .NULL)
    (by funext v; cases v <;> rfl) (by funext a; cases a <;> rfl) rfl
    (lawful_pointCodec (fun _ => rfl) (fun _ => .null))

/-- `e` and `p` gate on the *same* predicate applied to the *same* text, so each law
    reduces to that one decision. -/
theorem decimalCodec_e_num (x : WFNumeral) :
    decimalCodec.e (.num x) = if Numeral.Stored x.1 then some (.n x) else none := rfl

theorem decimalCodec_p_n (x : WFNumeral) :
    decimalCodec.p (.n x) = if Numeral.Stored x.1 then some (.num x) else none := rfl

theorem lawful_decimalCodec : Lawful decimalCodec := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t a he
    cases t with
    | num x =>
      rw [decimalCodec_e_num] at he
      by_cases hw : Numeral.Stored x.1 = true
      · rw [if_pos hw] at he; cases he; rw [decimalCodec_p_n, if_pos hw]
      · rw [if_neg hw] at he; exact nomatch he
    | _ => exact nomatch he
  · intro a t hp
    cases a with
    | n x =>
      rw [decimalCodec_p_n] at hp
      by_cases hw : Numeral.Stored x.1 = true
      · rw [if_pos hw] at hp; cases hp; rw [decimalCodec_e_num, if_pos hw]; rfl
      · rw [if_neg hw] at hp; exact nomatch hp
    | _ => exact nomatch hp
  · intro μ hμ t a he
    cases t with
    | num x =>
      rw [decimalCodec_e_num] at he
      by_cases hw : Numeral.Stored x.1 = true
      · rw [if_pos hw] at he; cases he; cases hμ; rfl
      · rw [if_neg hw] at he; exact nomatch he
    | _ => exact nomatch he
  · intro a t a' hp he
    cases a with
    | n x =>
      rw [decimalCodec_p_n] at hp
      by_cases hw : Numeral.Stored x.1 = true
      · rw [if_pos hw] at hp
        cases hp
        rw [decimalCodec_e_num, if_pos hw] at he
        cases he
        exact .n ..
      · rw [if_neg hw] at hp; exact nomatch hp
    | _ => exact nomatch hp

/-! ### `number` against the store (§1)

The other side of `decimal`'s answer, and the reason §1 states the condition as an inclusion
rather than as an equality. -/

/-! **~~survivesStore_numberCodec~~ is retired, and what killed it is worth stating.** It said
`number` survives a normalising store for free, because its `p` factored through the host's
`ofDec`: the store could rewrite the digits and the double read back the same. That was a
property of the DOUBLE CARRIER, not of `number`. Carrying `N` exactly makes `numberCodec.p` a
constructor wrapper, so its kernel is equality and a store that rewrites `"1.500"` to `"1.5"`
moves the value.

So the two numeric terms no longer differ in how they meet the store. They differ in one thing,
which is the thing they were always for: `decimal` gates at `Stored`, the store's own fixpoint,
and `survivesStore_decimalCodec` below is that. `number` accepts everything §1 accepts and makes
no promise about what comes back. -/

/-- §1: `decimal`'s `ker p` is equality — its `p` is the identity on the digits. -/
theorem ker_decimalCodec {x y : WFNumeral} (h : decimalCodec.Ker (.n x) (.n y))
    (hx : Numeral.Stored x.1 = true) : x.1 = y.1 := by
  have h' : decimalCodec.p (.n x) = decimalCodec.p (.n y) := h
  rw [decimalCodec_p_n, decimalCodec_p_n, if_pos hx] at h'
  by_cases hy : Numeral.Stored y.1 = true
  · rw [if_pos hy] at h'
    exact congrArg Subtype.val (Value.num.inj (Option.some.inj h'))
  · rw [if_neg hy] at h'; exact nomatch h'

/-- §1: `Can(decimal)` is the normal forms and a normalisation fixes its own, so `Stored`
    discharges `η ⊆ ker p`. Necessity is `not_survivesStore_numberCodec`. -/
theorem survivesStore_decimalCodec {η : Attr → Attr}
    (hη : ∀ s : WFNumeral, Numeral.Stored s.1 = true → η (.n s) = .n s) :
    SurvivesStore decimalCodec η := by
  rintro a ⟨v, hv⟩
  cases v with
  | num x =>
    rw [decimalCodec_e_num] at hv
    by_cases hs : Numeral.Stored x.1 = true
    · rw [if_pos hs] at hv
      cases hv
      show decimalCodec.p (η (.n x)) = decimalCodec.p (.n x)
      rw [hη x hs]
    · rw [if_neg hs] at hv; exact nomatch hv
  | _ => exact nomatch hv

/-- **The `(number)` case, and it no longer consumes an axiom.** `e` and `p` are mutually
    inverse constructor wrappers over one carrier, so all four laws are `rfl` at the only
    inhabited row. The shortest-text round trip this used to spend is not needed, because
    there is no host spelling to round-trip through. -/
theorem lawful_numberCodec : Lawful numberCodec := by
  refine ⟨?_, ?_, ?_, ?_⟩
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
  · intro a t a' hp he
    cases a with
    | n x => cases hp; cases he; exact .n ..
    | _ => exact nomatch hp

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

/-- `held` preserves the full laws: the core lemma, plus `≼` through the iso. -/
theorem Lawful.through {c : Codec} (h : Lawful c) {f g : Value → Value}
    (hiso : IsoCancels c f g) :
    Lawful (c.through f g) :=
  { LawfulCore.through h.core hiso with
    agree := by
      intro a t a' hp he
      obtain ⟨w, hw, rfl⟩ := through_p.mp hp
      rw [through_e, hiso.2 w (h.canon hw)] at he
      exact h.agree hw he }

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
    agree := fun hp he => h.agree (restrict_p.mp hp).1 (restrict_e.mp he).2 }


/-- …and every base is lawful. -/
theorem lawful_baseCodec : ∀ k : GroundKind, Lawful (baseCodec k)
  | .string  => lawful_stringCodec
  | .number  => lawful_numberCodec
  | .decimal => lawful_decimalCodec
  | .boolean => lawful_booleanCodec
  | .binary  => lawful_binaryCodec
  | .null    => lawful_nullCodec

/-- …and so is each set base's element pair. `decimal` is the one that is not a
    `GroundKind`, which is why this is a second table rather than a composition. -/
theorem lawful_setBase : ∀ b : SetBase, Lawful b.elem
  | .string  => lawful_stringCodec
  | .number  => lawful_numberCodec
  | .decimal => lawful_decimalCodec
  | .binary  => lawful_binaryCodec

/-! ### The literal codec is lawful because its base is

`literal` adds a prism and nothing else, so all four laws come from `Lawful.restrict` — one
statement, because there is one codec. -/

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
