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
theorem decimalCodec_e_str (s : String) :
    decimalCodec.e (.str s)
      = if h : Numeral.Stored s then some (.n ⟨s, Numeral.stored_wf h⟩) else none := rfl

theorem decimalCodec_p_n (x : WFNumeral) :
    decimalCodec.p (.n x) = if Numeral.Stored x.1 then some (.str x.1) else none := rfl

theorem lawful_decimalCodec : Lawful decimalCodec := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t a he
    cases t with
    | str s =>
      rw [decimalCodec_e_str] at he
      by_cases hw : Numeral.Stored s = true
      · rw [dif_pos hw] at he; cases he; rw [decimalCodec_p_n, if_pos hw]
      · rw [dif_neg hw] at he; exact nomatch he
    | _ => exact nomatch he
  · intro a t hp
    cases a with
    | n x =>
      rw [decimalCodec_p_n] at hp
      by_cases hw : Numeral.Stored x.1 = true
      · rw [if_pos hw] at hp; cases hp; rw [decimalCodec_e_str, dif_pos hw]; rfl
      · rw [if_neg hw] at hp; exact nomatch hp
    | _ => exact nomatch hp
  · intro μ hμ t a he
    cases t with
    | str s =>
      rw [decimalCodec_e_str] at he
      by_cases hw : Numeral.Stored s = true
      · rw [dif_pos hw] at he; cases he; cases hμ; rfl
      · rw [dif_neg hw] at he; exact nomatch he
    | _ => exact nomatch he
  · intro a t a' hp he
    cases a with
    | n x =>
      rw [decimalCodec_p_n] at hp
      by_cases hw : Numeral.Stored x.1 = true
      · rw [if_pos hw] at hp
        cases hp
        rw [decimalCodec_e_str, dif_pos hw] at he
        cases he
        exact .n ..
      · rw [if_neg hw] at hp; exact nomatch hp
    | _ => exact nomatch hp

/-! ### `number` against the store (§1)

The other side of `decimal`'s answer, and the reason §1 states the condition as an inclusion
rather than as an equality. -/

/-- §1: `number` survives the store for free. Its `p` factors through `ofDec`, so the digits
    may be rewritten freely — the contrast with `ker_decimalCodec`, whose kernel is equality. -/
theorem survivesStore_numberCodec {η : Attr → Attr}
    (hη : ∀ x : WFNumeral, ∃ y : WFNumeral, η (.n x) = .n y ∧
      Double.ofDec y.1 = Double.ofDec x.1) :
    SurvivesStore numberCodec η := by
  rintro a ⟨v, hv⟩
  cases v with
  | num d =>
    rw [numberCodec_e_num] at hv
    by_cases hw : Numeral.WF d.toDec = true
    · rw [dif_pos hw] at hv
      cases hv
      obtain ⟨y, hy, hofd⟩ := hη ⟨d.toDec, hw⟩
      show numberCodec.p (η (.n ⟨d.toDec, hw⟩)) = numberCodec.p (.n ⟨d.toDec, hw⟩)
      rw [hy, numberCodec_p_n, numberCodec_p_n, hofd]
    · rw [dif_neg hw] at hv; exact nomatch hv
  | _ => exact nomatch hv

/-! ### `decimal` against the store (§1)

`SurvivesStore` is the premise; these two are `decimal`'s answer to it, and together they say
that narrowing the held set to `Numeral.Stored` was not merely *a* fix but the whole of one. -/

/-- §1: `decimal`'s `ker p` is equality — its `p` is the identity on the digits. -/
theorem ker_decimalCodec {x y : WFNumeral} (h : decimalCodec.Ker (.n x) (.n y))
    (hx : Numeral.Stored x.1 = true) : x.1 = y.1 := by
  have h' : decimalCodec.p (.n x) = decimalCodec.p (.n y) := h
  rw [decimalCodec_p_n, decimalCodec_p_n, if_pos hx] at h'
  by_cases hy : Numeral.Stored y.1 = true
  · rw [if_pos hy] at h'
    exact Value.str.inj (Option.some.inj h')
  · rw [if_neg hy] at h'; exact nomatch h'

/-- §1: `Can(decimal)` is the normal forms and a normalisation fixes its own, so `Stored`
    discharges `η ⊆ ker p`. Necessity is `not_survivesStore_wfDecimalCodec`. -/
theorem survivesStore_decimalCodec {η : Attr → Attr}
    (hη : ∀ s : WFNumeral, Numeral.Stored s.1 = true → η (.n s) = .n s) :
    SurvivesStore decimalCodec η := by
  rintro a ⟨v, hv⟩
  cases v with
  | str s =>
    rw [decimalCodec_e_str] at hv
    by_cases hs : Numeral.Stored s = true
    · rw [dif_pos hs] at hv
      cases hv
      show decimalCodec.p (η (.n ⟨s, _⟩)) = decimalCodec.p (.n ⟨s, _⟩)
      rw [hη ⟨s, Numeral.stored_wf hs⟩ hs]
    · rw [dif_neg hs] at hv; exact nomatch hv
  | _ => exact nomatch hv

/-- The `(number)` case — the one consuming the shortest-text axiom. -/
theorem lawful_numberCodec : Lawful numberCodec := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t a he
    cases t with
    | num d =>
      rw [numberCodec_e_num] at he
      by_cases hw : Numeral.WF d.toDec = true
      · rw [dif_pos hw] at he; cases he
        rw [numberCodec_p_n]
        show ((Double.ofDec (⟨d.toDec, hw⟩ : WFNumeral).1).bind
          (fun e => if Numeral.WF e.toDec then some (Value.num e) else none)) = some (.num d)
        rw [Double.roundtrip, Option.bind_some, if_pos hw]
      · rw [dif_neg hw] at he; exact nomatch he
    | _ => exact nomatch he
  · intro a t hp
    cases a with
    | n x =>
      rw [numberCodec_p_n] at hp
      cases hx : Double.ofDec x.1 with
      | none => rw [hx] at hp; exact nomatch hp
      | some d =>
        rw [hx] at hp
        replace hp : (if Numeral.WF d.toDec then some (Value.num d) else none) = some t := hp
        by_cases hw : Numeral.WF d.toDec = true
        · rw [if_pos hw] at hp; cases hp
          rw [numberCodec_e_num, dif_pos hw]; rfl
        · rw [if_neg hw] at hp; exact nomatch hp
    | _ => exact nomatch hp
  · intro μ hμ t a he
    cases t with
    | num d =>
      rw [numberCodec_e_num] at he
      by_cases hw : Numeral.WF d.toDec = true
      · rw [dif_pos hw] at he; cases he; cases hμ; rfl
      · rw [dif_neg hw] at he; exact nomatch he
    | _ => exact nomatch he
  · intro a t a' hp he
    cases a with
    | n x =>
      rw [numberCodec_p_n] at hp
      cases hx : Double.ofDec x.1 with
      | none => rw [hx] at hp; exact nomatch hp
      | some d =>
        rw [hx] at hp
        replace hp : (if Numeral.WF d.toDec then some (Value.num d) else none) = some t := hp
        by_cases hw : Numeral.WF d.toDec = true
        · rw [if_pos hw] at hp; cases hp
          rw [numberCodec_e_num, dif_pos hw] at he
          cases he
          exact .n ..
        · rw [if_neg hw] at hp; exact nomatch hp
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
theorem lawful_literalCodec (k : GroundKind) (ls : NEFinset k.Carrier) :
    Lawful (literalCodec k ls) :=
  Lawful.congr (d := (baseCodec k).restrict (inL k ls)) rfl rfl rfl
    (Lawful.restrict (lawful_baseCodec k) (inL k ls))

theorem LawfulCore.extendRead {c : Codec} (h : LawfulCore c) {r : Attr → Option Value}
    (hran : ∀ a v, r a = some v → (c.e v).isSome) :
    LawfulCore (c.extendRead r) where
  retract he := extendRead_p.mpr (.inl (h.retract (extendRead_e.mp he)))
  canon hp := (extendRead_p.mp hp).elim h.canon fun ⟨_, hr⟩ => hran _ _ hr
  writes := by intro μ hμ t a he; exact h.writes hμ (extendRead_e.mp he)

/-- `nullable` keeps the core laws under null-honesty. Structurally this is the sum
    `alt [c, null-point]`; the honesty premises are its (U), specialised — and they are
    used in exactly one place each, to rule out the wrapper's own point colliding with
    the base's. -/
theorem LawfulCore.orNull {c : Codec} (h : LawfulCore c) (hn : NullHonest c) :
    LawfulCore c.orNull where
  retract he := by
    rcases orNull_e.mp he with ⟨rfl, rfl⟩ | ⟨hv, hc⟩
    · exact orNull_p.mpr (.inl ⟨rfl, rfl⟩)
    · exact orNull_p.mpr (.inr ⟨fun hz => hv (hn.1 _ _ hc hz), h.retract hc⟩)
  canon hp := by
    rcases orNull_p.mp hp with ⟨rfl, rfl⟩ | ⟨ha, hc⟩
    · exact Option.isSome_iff_exists.mpr ⟨.null, orNull_e.mpr (.inl ⟨rfl, rfl⟩)⟩
    · obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (h.canon hc)
      exact Option.isSome_iff_exists.mpr
        ⟨a', orNull_e.mpr (.inr ⟨fun hz => ha (hn.2 _ _ hc hz), ha'⟩)⟩
  writes := by intro μ hμ; exact nomatch hμ

/-- `nullable` preserves the full laws: the core lemma, plus `≼` — read-honesty is
    what keeps a non-`NULL` attribute from re-encoding as `⟨NULL, ∗⟩`. -/
theorem Lawful.orNull {c : Codec} (h : Lawful c) (hn : NullHonest c) :
    Lawful c.orNull :=
  { LawfulCore.orNull h.core hn with
    agree := by
      intro a t a' hp he
      rcases orNull_p.mp hp with ⟨rfl, rfl⟩ | ⟨ha, hc⟩
      · rcases orNull_e.mp he with ⟨-, rfl⟩ | ⟨hv, -⟩
        · exact .null
        · exact absurd rfl hv
      · rcases orNull_e.mp he with ⟨rfl, -⟩ | ⟨-, hc'⟩
        · exact absurd (hn.2 _ _ hc rfl) ha
        · exact h.agree hc hc' }

/-! ### `nullable`, as the sugar it is

§3 gives `nullable(c)` a dichotomy: where `c` does not touch the null point it *is*
`union(c, ⟨NULL⟩-point)`, and where `c` does touch it the wrapper adds nothing at all.
`withNull` makes that the *definition* — add the point unless it is already there — and
the two honesty premises stop being premises. They were doing (U)'s job for a
two-option sum by hand; the guard lets lawfulness do it instead. -/

/-- Where `c` does not own the null point, neither half can reach it. -/
theorem ownsNull_false {c : Codec} (hn : c.ownsNull = false) :
    c.e .null = none ∧ c.p .null = none := by
  simp only [Codec.ownsNull, Bool.or_eq_false_iff] at hn
  constructor
  · cases h : c.e .null with
    | none => rfl
    | some _ => rw [h] at hn; exact nomatch hn.1
  · cases h : c.p .null with
    | none => rfl
    | some _ => rw [h] at hn; exact nomatch hn.2

/-- **§3's null-honesty is a consequence, not a premise.** Under the guard, a lawful `c`
    cannot write `⟨NULL, ∗⟩` — (R) would make it read the point straight back — and
    cannot read to `null` — (C) would make it write the point. Both hypotheses are
    refuted rather than assumed. -/
theorem nullHonest_of_not_ownsNull {c : Codec} (h : LawfulCore c)
    (hn : c.ownsNull = false) : NullHonest c := by
  obtain ⟨he, hp⟩ := ownsNull_false hn
  refine ⟨fun v a hv hz => ?_, fun a v hv hz => ?_⟩
  · subst hz; rw [h.retract hv] at hp; exact nomatch hp
  · subst hz
    have hc := h.canon hv
    rw [he] at hc; exact nomatch hc

/-- §3 `(nullable)`: add the null point unless `c` already owns it. `T` and `μ` do not
    depend on the guard — the rule concludes `T + 𝟙 ⇝ ⊤` either way; only the pair moves. -/
def Codec.withNull (c : Codec) : Codec :=
  { T := fun v => c.T v ∨ v = .null
    μ := none
    e := if c.ownsNull then c.e else addPoint (· matches .null) .null c.e
    p := if c.ownsNull then c.p else addPoint (· matches .null) .null c.p }

/-- Where `c` does not own the point, the wrapper *is* `orNull` — §3's first branch. -/
theorem withNull_eq_orNull {c : Codec} (h : c.ownsNull = false) : c.withNull = c.orNull := by
  simp only [Codec.withNull, Codec.orNull, h, if_false, Bool.false_eq_true]
  rfl

/-- …and where it does, the wrapper adds nothing to the pair — §3's second branch,
    `orNull_eq_self` made definitional. -/
theorem withNull_e_of_owns {c : Codec} (h : c.ownsNull = true) : c.withNull.e = c.e := by
  simp only [Codec.withNull, h, if_true]

theorem withNull_p_of_owns {c : Codec} (h : c.ownsNull = true) : c.withNull.p = c.p := by
  simp only [Codec.withNull, h, if_true]

/-- §3 `(nullable)` keeps the core laws, with **no** honesty premise. -/
theorem lawfulCore_withNull {c : Codec} (h : LawfulCore c) :
    LawfulCore c.withNull := by
  cases hw : c.ownsNull with
  | false => exact withNull_eq_orNull hw ▸ h.orNull (nullHonest_of_not_ownsNull h hw)
  | true =>
    exact { retract := fun he => by
              rw [withNull_p_of_owns hw]; rw [withNull_e_of_owns hw] at he; exact h.retract he
            canon := fun hp => by
              rw [withNull_e_of_owns hw]; rw [withNull_p_of_owns hw] at hp; exact h.canon hp
            writes := fun hμ => nomatch hμ }

/-- …and the full laws, likewise premise-free. -/
theorem lawful_withNull {c : Codec} (h : Lawful c) : Lawful c.withNull := by
  cases hw : c.ownsNull with
  | false =>
    exact withNull_eq_orNull hw ▸ h.orNull (nullHonest_of_not_ownsNull h.core hw)
  | true =>
    exact { lawfulCore_withNull h.core with
            agree := fun hp he => by
              rw [withNull_p_of_owns hw] at hp; rw [withNull_e_of_owns hw] at he
              exact h.agree hp he }

/-- The carrier survives the guard: the held set gains the null point in both branches. -/
theorem carrier_withNull {c : Codec} (h : Carrier c) : Carrier c.withNull := by
  cases hw : c.ownsNull with
  | false => exact withNull_eq_orNull hw ▸ carrier_orNull h
  | true =>
    exact { domE := fun he => by rw [withNull_e_of_owns hw] at he; exact Or.inl (h.domE he)
            ranP := fun hp => by rw [withNull_p_of_owns hw] at hp; exact Or.inl (h.ranP hp) }

/-- §6's idempotence row, **by construction**: the wrapper's own point makes the second
    insertion find it present, so the pair is untouched. It needed null-honesty to be
    lawful; now it needs nothing. -/
theorem withNull_ownsNull {c : Codec} : c.withNull.ownsNull = true := by
  cases hw : c.ownsNull with
  | false =>
    have he : c.withNull.e .null = some .null := by simp [Codec.withNull, addPoint, hw]
    simp [Codec.ownsNull, he]
  | true =>
    rw [Codec.ownsNull, withNull_e_of_owns hw, withNull_p_of_owns hw]
    exact hw

theorem withNull_idem_e {c : Codec} : c.withNull.withNull.e = c.withNull.e :=
  withNull_e_of_owns withNull_ownsNull

theorem withNull_idem_p {c : Codec} : c.withNull.withNull.p = c.withNull.p :=
  withNull_p_of_owns withNull_ownsNull

end

end Calculus
