import Calculus.Dynamo.Alg.Lawful

/-!
# Lawfulness — the open frontier

The laws that are stated and not yet discharged, and the ones whose discharge is partial.
`docs/roadmap.md` says which of these is a future state and what decides it.
-/

namespace Calculus

noncomputable section
/-! ## Lawfulness — the open frontier (README roadmap) -/

/-! ### `setCodec`'s laws

Every one of these was a traversal argument over a list; on `Finset` they are the element
codec's own laws lifted by `setImage_inv`. What used to need ~~asWireSet~~'s three-way
payload split and a non-emptiness side condition needs neither: the split is the three
constructors, and non-emptiness is `Finset.Nonempty`. -/

/-- The three wire prisms invert as `setImage_roundTrip` wants. -/
theorem sC_out_inj (a : Attr) (b : String) (h : sC.out a = some b) : a = .s b := by
  cases a <;> simp_all [sC]
theorem nC_out_inj (a : Attr) (b : WFNumeral) (h : nC.out a = some b) : a = .n b := by
  cases a <;> simp_all [nC]
theorem bC_out_inj (a : Attr) (b : Bytes) (h : bC.out a = some b) : a = .b b := by
  cases a <;> simp_all [bC]

/-- A payload projection pins the member. -/
theorem member_of_sC {a : Attr} (h : (sC.out a).isSome = true) : a.member = .S := by
  cases a <;> simp_all [sC, Attr.member]
theorem member_of_nC {a : Attr} (h : (nC.out a).isSome = true) : a.member = .N := by
  cases a <;> simp_all [nC, Attr.member]
theorem member_of_bC {a : Attr} (h : (bC.out a).isSome = true) : a.member = .B := by
  cases a <;> simp_all [bC, Attr.member]


export Alg (setImage_read)

/-- `decSet` lands on the string branch when the reads produce strings. -/
theorem decSet_strBranch {α : Type} {c : Codec} {inj : α → Attr} {S : NEFinset α}
    {U : NEFinset String}
    (h1 : neSetImage (fun y => (c.p (inj y)).bind vStr) S = some U) :
    decSet c inj S = some (.strSet U) := by
  unfold decSet; rw [h1]

/-- …the numeric branch when they produce numbers, the string branch having failed. -/
theorem decSet_numBranch {α : Type} {c : Codec} {inj : α → Attr} {S : NEFinset α}
    {U : NEFinset WFNumeral}
    (h0 : neSetImage (fun y => (c.p (inj y)).bind vStr) S = none)
    (h1 : neSetImage (fun y => (c.p (inj y)).bind vNum) S = some U) :
    decSet c inj S = some (.numSet U) := by
  unfold decSet; rw [h0, h1]

/-- …and the binary branch when both earlier ones have. -/
theorem decSet_binBranch {α : Type} {c : Codec} {inj : α → Attr} {S : NEFinset α}
    {U : NEFinset Bytes}
    (h0 : neSetImage (fun y => (c.p (inj y)).bind vStr) S = none)
    (h0' : neSetImage (fun y => (c.p (inj y)).bind vNum) S = none)
    (h1 : neSetImage (fun y => (c.p (inj y)).bind vBin) S = some U) :
    decSet c inj S = some (.binSet U) := by
  unfold decSet; rw [h0, h0', h1]; rfl

/-- **(R) for `set`.** The wire image inverts by `setImage_inv`, and the read side lands on
    the branch the element codec's own reads determine — the *value* kind fixes it, whichever
    wire member the write happened to use. -/
theorem set_retract {c : Codec} (h : LawfulCore c) :
    ∀ {t a}, (setCodec c).e t = some a → (setCodec c).p a = some t := by
  -- Both helpers lose a `Nonempty` argument: `℘⁺fin` carries it, so `key` returns only
  -- the round trip and `miss` takes its witness from `T.2`.
  have key : ∀ {α β : Type} [DecidableEq α] [DecidableEq β]
      {vinj : α → Value} {aout : Attr → Option β} {ainj : β → Attr}
      {vout : Value → Option α},
      (∀ a b, aout a = some b → a = ainj b) → (∀ x, vout (vinj x) = some x) →
      ∀ {S : NEFinset α} {T : NEFinset β},
        neSetImage (fun x => (c.e (vinj x)).bind aout) S = some T →
        neSetImage (fun y => (c.p (ainj y)).bind vout) T = some S := by
    intro α β _ _ vinj aout ainj vout hA hV S T hI
    exact neSetImage_eq_setImage.mpr
      (setImage_roundTrip h hA hV (neSetImage_eq_setImage.mp hI))
  have miss : ∀ {α β γ : Type} [DecidableEq β] [DecidableEq γ]
      {vinj : α → Value} {aout : Attr → Option β} {ainj : β → Attr}
      {vout : Value → Option γ},
      (∀ a b, aout a = some b → a = ainj b) → (∀ x, vout (vinj x) = none) →
      ∀ {S : NEFinset α} {T : NEFinset β},
        neSetImage (fun x => (c.e (vinj x)).bind aout) S = some T →
        neSetImage (fun y => (c.p (ainj y)).bind vout) T = none := by
    intro α β γ _ _ vinj aout ainj vout hA hV S T hI
    obtain ⟨y, hy⟩ := T.2
    obtain ⟨x, -, hpx⟩ := setImage_read h hA (neSetImage_eq_setImage.mp hI) y hy
    exact neSetImage_none (setImage_none_of hy (by rw [hpx]; simpa using hV x))
  intro t a he
  rcases setCodec_e_eq.mp he with ⟨S, rfl, hE⟩ | ⟨S, rfl, hE⟩ | ⟨S, rfl, hE⟩ <;>
    (unfold encSet at hE
     split at hE
     · next T hT =>
       injection hE with hE; subst hE
       first
       | exact decSet_strBranch
           (key (vinj := Value.str) (vout := vStr) sC_out_inj (fun _ => rfl) hT)
       | exact decSet_numBranch
           (miss (vinj := Value.num) (vout := vStr) sC_out_inj (fun _ => rfl) hT)
           (key (vinj := Value.num) (vout := vNum) sC_out_inj (fun _ => rfl) hT)
       | exact decSet_binBranch
           (miss (vinj := Value.bin) (vout := vStr) sC_out_inj (fun _ => rfl) hT)
           (miss (vinj := Value.bin) (vout := vNum) sC_out_inj (fun _ => rfl) hT)
           (key (vinj := Value.bin) (vout := vBin) sC_out_inj (fun _ => rfl) hT)
     · split at hE
       · next T hT =>
         injection hE with hE; subst hE
         first
         | exact decSet_strBranch
             (key (vinj := Value.str) (vout := vStr) nC_out_inj (fun _ => rfl) hT)
         | exact decSet_numBranch
             (miss (vinj := Value.num) (vout := vStr) nC_out_inj (fun _ => rfl) hT)
             (key (vinj := Value.num) (vout := vNum) nC_out_inj (fun _ => rfl) hT)
         | exact decSet_binBranch
             (miss (vinj := Value.bin) (vout := vStr) nC_out_inj (fun _ => rfl) hT)
             (miss (vinj := Value.bin) (vout := vNum) nC_out_inj (fun _ => rfl) hT)
             (key (vinj := Value.bin) (vout := vBin) nC_out_inj (fun _ => rfl) hT)
       · next =>
         obtain ⟨T, hT, hA⟩ := Option.map_eq_some_iff.mp hE
         subst hA
         first
         | exact decSet_strBranch
             (key (vinj := Value.str) (vout := vStr) bC_out_inj (fun _ => rfl) hT)
         | exact decSet_numBranch
             (miss (vinj := Value.num) (vout := vStr) bC_out_inj (fun _ => rfl) hT)
             (key (vinj := Value.num) (vout := vNum) bC_out_inj (fun _ => rfl) hT)
         | exact decSet_binBranch
             (miss (vinj := Value.bin) (vout := vStr) bC_out_inj (fun _ => rfl) hT)
             (miss (vinj := Value.bin) (vout := vNum) bC_out_inj (fun _ => rfl) hT)
             (key (vinj := Value.bin) (vout := vBin) bC_out_inj (fun _ => rfl) hT))

/-- **(W) for `set`.** The wire member is `setMember` of the element's, and which branch
    `encSet` took is fixed by the element codec's own member. -/
theorem set_writes {c : Codec} (h : LawfulCore c) :
    ∀ {μ}, (setCodec c).μ = some μ → ∀ {t a}, (setCodec c).e t = some a →
      a.member = μ := by
  intro μ hμ t a he
  replace hμ : c.μ.bind setMember = some μ := hμ
  cases hc : c.μ with
  | none => rw [hc] at hμ; exact nomatch hμ
  | some μ₀ =>
    rw [hc] at hμ
    replace hμ : setMember μ₀ = some μ := hμ
    rcases setCodec_e_eq.mp he with ⟨S, rfl, hE⟩ | ⟨S, rfl, hE⟩ | ⟨S, rfl, hE⟩ <;>
      · obtain ⟨x₀, hx₀⟩ := S.2
        obtain ⟨a₀, ha₀⟩ := Option.isSome_iff_exists.mp (encSet_elem hE x₀ hx₀)
        have hm₀ : a₀.member = μ₀ := h.writes hc ha₀
        unfold encSet at hE
        split at hE
        · next T hT =>
          injection hE with hE; subst hE
          have hs := setImage_some (neSetImage_eq_setImage.mp hT) x₀ hx₀
          rw [ha₀] at hs
          rw [← hm₀, member_of_sC hs] at hμ
          simpa [Attr.member] using Option.some.inj hμ
        · split at hE
          · next T hT =>
            injection hE with hE; subst hE
            have hs := setImage_some (neSetImage_eq_setImage.mp hT) x₀ hx₀
            rw [ha₀] at hs
            rw [← hm₀, member_of_nC hs] at hμ
            simpa [Attr.member] using Option.some.inj hμ
          · next =>
            obtain ⟨T, hT, hA⟩ := Option.map_eq_some_iff.mp hE
            subst hA
            have hs := setImage_some (neSetImage_eq_setImage.mp hT) x₀ hx₀
            rw [ha₀] at hs
            rw [← hm₀, member_of_bC hs] at hμ
            simpa [Attr.member] using Option.some.inj hμ

/-- Writing a set succeeds when its elements do and the element member is ground: the
    member fixes which branch `encSet` takes, and (R) supplies the injectivity. -/
theorem encSet_isSome_of {α : Type} {c : Codec} (h : LawfulCore c)
    {μ₀ μS : Member} (hsm : setMember μ₀ = some μS)
    {vinj : α → Value} (hvi : ∀ x y, vinj x = vinj y → x = y)
    {S : NEFinset α}
    (hall : ∀ x ∈ S.1, (c.e (vinj x)).isSome = true)
    (hmem : ∀ x ∈ S.1, ∀ a', c.e (vinj x) = some a' → a'.member = μ₀) :
    (encSet c vinj S).isSome = true := by
  obtain ⟨x₀, hx₀⟩ := S.2
  unfold encSet
  -- the element member decides the branch
  cases μ₀
  case S =>
    have hb : ∀ x ∈ S.1, ((c.e (vinj x)).bind sC.out).isSome = true := by
      intro x hx
      obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (hall x hx)
      have := hmem x hx _ ha'
      cases a' <;> simp_all [sC, Attr.member]
    have hinj : ∀ x₁ ∈ S.1, ∀ x₂ ∈ S.1, ∀ y,
        (c.e (vinj x₁)).bind sC.out = some y → (c.e (vinj x₂)).bind sC.out = some y →
        x₁ = x₂ := by
      intro x₁ _ x₂ _ y h1 h2
      simp only [Option.bind_eq_some_iff] at h1 h2
      obtain ⟨a₁, he₁, ho₁⟩ := h1
      obtain ⟨a₂, he₂, ho₂⟩ := h2
      rw [sC_out_inj a₁ y ho₁] at he₁
      rw [sC_out_inj a₂ y ho₂] at he₂
      exact hvi _ _ ((h.retract he₁).symm.trans (h.retract he₂) |> Option.some.inj)
    obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp (setImage_isSome_of hb hinj)
    rw [(neSetImage_eq_setImage (T := ⟨T, setImage_nonempty hT S.2⟩)).mpr hT]; rfl
  case N =>
    have hb : ∀ x ∈ S.1, ((c.e (vinj x)).bind sC.out).isSome = true → False := by
      intro x hx hcon
      obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (hall x hx)
      have := hmem x hx _ ha'
      rw [ha'] at hcon
      cases a' <;> simp_all [sC, Attr.member]
    have hb2 : ∀ x ∈ S.1, ((c.e (vinj x)).bind nC.out).isSome = true := by
      intro x hx
      obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (hall x hx)
      have := hmem x hx _ ha'
      cases a' <;> simp_all [nC, Attr.member]
    have hinj : ∀ x₁ ∈ S.1, ∀ x₂ ∈ S.1, ∀ y,
        (c.e (vinj x₁)).bind nC.out = some y → (c.e (vinj x₂)).bind nC.out = some y →
        x₁ = x₂ := by
      intro x₁ _ x₂ _ y h1 h2
      simp only [Option.bind_eq_some_iff] at h1 h2
      obtain ⟨a₁, he₁, ho₁⟩ := h1
      obtain ⟨a₂, he₂, ho₂⟩ := h2
      rw [nC_out_inj a₁ y ho₁] at he₁
      rw [nC_out_inj a₂ y ho₂] at he₂
      exact hvi _ _ ((h.retract he₁).symm.trans (h.retract he₂) |> Option.some.inj)
    have hfail : setImage (fun x => (c.e (vinj x)).bind sC.out) S = none :=
      setImage_none_of hx₀ (by
        cases hcon : (c.e (vinj x₀)).bind sC.out with
        | none => rfl
        | some _ => exact absurd (by rw [hcon]; rfl) (fun hh => hb x₀ hx₀ hh))
    obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp (setImage_isSome_of hb2 hinj)
    rw [neSetImage_none hfail,
      (neSetImage_eq_setImage (T := ⟨T, setImage_nonempty hT S.2⟩)).mpr hT]; rfl
  case B =>
    have hfailS : setImage (fun x => (c.e (vinj x)).bind sC.out) S = none :=
      setImage_none_of hx₀ (by
        obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (hall x₀ hx₀)
        have := hmem x₀ hx₀ _ ha'
        cases a' <;> simp_all [sC, Attr.member])
    have hfailN : setImage (fun x => (c.e (vinj x)).bind nC.out) S = none :=
      setImage_none_of hx₀ (by
        obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (hall x₀ hx₀)
        have := hmem x₀ hx₀ _ ha'
        cases a' <;> simp_all [nC, Attr.member])
    have hb : ∀ x ∈ S.1, ((c.e (vinj x)).bind bC.out).isSome = true := by
      intro x hx
      obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (hall x hx)
      have := hmem x hx _ ha'
      cases a' <;> simp_all [bC, Attr.member]
    have hinj : ∀ x₁ ∈ S.1, ∀ x₂ ∈ S.1, ∀ y,
        (c.e (vinj x₁)).bind bC.out = some y → (c.e (vinj x₂)).bind bC.out = some y →
        x₁ = x₂ := by
      intro x₁ _ x₂ _ y h1 h2
      simp only [Option.bind_eq_some_iff] at h1 h2
      obtain ⟨a₁, he₁, ho₁⟩ := h1
      obtain ⟨a₂, he₂, ho₂⟩ := h2
      rw [bC_out_inj a₁ y ho₁] at he₁
      rw [bC_out_inj a₂ y ho₂] at he₂
      exact hvi _ _ ((h.retract he₁).symm.trans (h.retract he₂) |> Option.some.inj)
    obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp (setImage_isSome_of hb hinj)
    rw [neSetImage_none hfailS, neSetImage_none hfailN,
      (neSetImage_eq_setImage (T := ⟨T, setImage_nonempty hT S.2⟩)).mpr hT]; rfl
  all_goals exact nomatch hsm


/-- `encSet` writes a string set when the element writes produce strings. -/
theorem encSet_ssBranch {α : Type} {c : Codec} {inj : α → Value} {S : NEFinset α}
    {T : NEFinset String}
    (h1 : neSetImage (fun x => (c.e (inj x)).bind sC.out) S = some T) :
    encSet c inj S = some (.ss T) := by
  unfold encSet; rw [h1]

/-- …a number set when they produce numbers, the string branch having failed. -/
theorem encSet_nsBranch {α : Type} {c : Codec} {inj : α → Value} {S : NEFinset α}
    {T : NEFinset WFNumeral}
    (h0 : neSetImage (fun x => (c.e (inj x)).bind sC.out) S = none)
    (h1 : neSetImage (fun x => (c.e (inj x)).bind nC.out) S = some T) :
    encSet c inj S = some (.ns T) := by
  unfold encSet; rw [h0, h1]

/-- …and a binary set when both earlier ones have. -/
theorem encSet_bsBranch {α : Type} {c : Codec} {inj : α → Value} {S : NEFinset α}
    {T : NEFinset Bytes}
    (h0 : neSetImage (fun x => (c.e (inj x)).bind sC.out) S = none)
    (h0' : neSetImage (fun x => (c.e (inj x)).bind nC.out) S = none)
    (h1 : neSetImage (fun x => (c.e (inj x)).bind bC.out) S = some T) :
    encSet c inj S = some (.bs T) := by
  unfold encSet; rw [h0, h0', h1]; rfl

/-- **Canonical reads for `set`.** The mirror of `set_retract`: the read image inverts by
    `setImage_inv`, and the write lands on the wire member of the attribute that was read. -/
theorem set_canon {c : Codec} (h : Lawful c) :
    ∀ {a t}, (setCodec c).p a = some t → (setCodec c).e t = some a := by
  have key : ∀ {α β : Type} [DecidableEq α] [DecidableEq β]
      {vinj : β → Value} {aout : Attr → Option α} {ainj : α → Attr}
      {vout : Value → Option β},
      (∀ y, aout (ainj y) = some y) → (∀ o x, o.bind vout = some x → o = some (vinj x)) →
      ∀ {S : NEFinset α} {U : NEFinset β},
        neSetImage (fun y => (c.p (ainj y)).bind vout) S = some U →
        neSetImage (fun x => (c.e (vinj x)).bind aout) U = some S := by
    intro α β _ _ vinj aout ainj vout hA hV S U hI
    refine neSetImage_eq_setImage.mpr (setImage_inv (fun y x hxy => ?_)
      (neSetImage_eq_setImage.mp hI))
    rw [h.canon (hV _ x hxy)]
    exact hA y
  have miss : ∀ {α β γ : Type} [DecidableEq β] [DecidableEq γ]
      {vinj : β → Value} {aout : Attr → Option γ} {ainj : α → Attr}
      {vout : Value → Option β},
      (∀ y, aout (ainj y) = none) → (∀ o x, o.bind vout = some x → o = some (vinj x)) →
      ∀ {S : NEFinset α} {U : NEFinset β},
        neSetImage (fun y => (c.p (ainj y)).bind vout) S = some U →
        neSetImage (fun x => (c.e (vinj x)).bind aout) U = none := by
    intro α β γ _ _ vinj aout ainj vout hA hV S U hI
    obtain ⟨x, hx⟩ := U.2
    obtain ⟨y, -, hy⟩ := (mem_setImage (neSetImage_eq_setImage.mp hI) x).mp hx
    exact neSetImage_none (setImage_none_of hx (by rw [h.canon (hV _ x hy)]; exact hA y))
  have hs : ∀ o x, o.bind vStr = some x → o = some (Value.str x) := fun _ _ => bind_vStr
  have hn : ∀ o x, o.bind vNum = some x → o = some (Value.num x) := fun _ _ => bind_vNum
  have hb : ∀ o x, o.bind vBin = some x → o = some (Value.bin x) := fun _ _ => bind_vBin
  intro a t hp
  rcases setCodec_p_eq.mp hp with ⟨S, rfl, hD⟩ | ⟨S, rfl, hD⟩ | ⟨S, rfl, hD⟩ <;>
    (unfold decSet at hD
     split at hD
     · next U hU =>
       injection hD with hD; subst hD
       first
       | exact encSet_ssBranch (key (aout := sC.out) (fun _ => rfl) hs hU)
       | exact encSet_nsBranch (miss (aout := sC.out) (fun _ => rfl) hs hU)
           (key (aout := nC.out) (fun _ => rfl) hs hU)
       | exact encSet_bsBranch (miss (aout := sC.out) (fun _ => rfl) hs hU)
           (miss (aout := nC.out) (fun _ => rfl) hs hU)
           (key (aout := bC.out) (fun _ => rfl) hs hU)
     · split at hD
       · next U hU =>
         injection hD with hD; subst hD
         first
         | exact encSet_ssBranch (key (aout := sC.out) (fun _ => rfl) hn hU)
         | exact encSet_nsBranch (miss (aout := sC.out) (fun _ => rfl) hn hU)
             (key (aout := nC.out) (fun _ => rfl) hn hU)
         | exact encSet_bsBranch (miss (aout := sC.out) (fun _ => rfl) hn hU)
             (miss (aout := nC.out) (fun _ => rfl) hn hU)
             (key (aout := bC.out) (fun _ => rfl) hn hU)
       · next =>
         obtain ⟨U, hU, hA⟩ := Option.map_eq_some_iff.mp hD
         subst hA
         first
         | exact encSet_ssBranch (key (aout := sC.out) (fun _ => rfl) hb hU)
         | exact encSet_nsBranch (miss (aout := sC.out) (fun _ => rfl) hb hU)
             (key (aout := nC.out) (fun _ => rfl) hb hU)
         | exact encSet_bsBranch (miss (aout := sC.out) (fun _ => rfl) hb hU)
             (miss (aout := nC.out) (fun _ => rfl) hb hU)
             (key (aout := bC.out) (fun _ => rfl) hb hU))

/-- **`setCodec` is lawful.** The member law comes from `set_writes`, and canonical reads from
    `set_canon`; neither needs the element codec's index. -/
theorem lawful_setCodec {c : Codec} (h : Lawful c) : Lawful (setCodec c) :=
  .ofRC (set_retract h.core) (set_canon h) (set_writes h.core)


/-! ### The keyed product

The guards, the entry steps, the rest policy and the two clauses of §2 read no carrier
constructor, so they are the generic layer's. The aliases give them their names here, and the
two laws below are the generic ones at the `map` and `M` prisms. -/

export Alg (valPresentB_of)

/-- The keyed product — the doc's current-schema `object`. -/
theorem lawful_objectCodec {sems : MapOf FieldSem} {rest : RestSem}
    (hf : ∀ k, Lawful (sems.2 k).codec)
    (hrest : ∀ c, rest = .codec c → Lawful c) (hnd : rest ≠ .drop) :
    Lawful (objectCodec sems rest) :=
  Alg.lawful_objectCodec (fun _ => rfl) hf hrest hnd

/-! ### Kind separation, and `opaque`'s fixpoint

    The discharger `(opaque)` needs. An option is
    *pinned to a kind* when it admits only values and attributes of that kind — which is
    precisely what §3 means by calling `opaque`'s options "self-identifying". Pin each
    option and keep the kinds distinct, and compatibility follows with nothing said
    about what the options contain: `onKind_set` and its two neighbours hold for *any*
    element codec, which is why the fixpoint needs nothing from the recursive call. -/

/-- An option pinned to a kind: it admits only values and attributes of that kind. -/
def Codec.OnKind (o : Codec) (k : Kind) : Prop :=
  (∀ v, (o.e v).isSome = true → v.kind = k) ∧ (∀ a, (o.p a).isSome = true → a.kind = k)

/-! ### `opaque`'s options, each pinned to its kind -/

theorem onKind_string : Codec.OnKind (stringCodec) .string := by
  constructor <;> intro x hx <;> cases x <;>
    simp_all [stringCodec, Value.kind, Attr.kind]

theorem onKind_boolean : Codec.OnKind (booleanCodec) .boolean := by
  constructor <;> intro x hx <;> cases x <;>
    simp_all [booleanCodec, Value.kind, Attr.kind]

theorem onKind_binary : Codec.OnKind (binaryCodec) .binary := by
  constructor <;> intro x hx <;> cases x <;>
    simp_all [binaryCodec, Value.kind, Attr.kind]

theorem onKind_null : Codec.OnKind (nullCodec) .null := by
  constructor <;> intro x hx <;> cases x <;>
    simp_all [nullCodec, Value.kind, Attr.kind]

/-- The number option is pinned to `number`. -/
theorem onKind_number : Codec.OnKind (numberCodec) .number := by
  constructor <;> intro x hx <;> cases x <;>
    simp_all [numberCodec, Value.kind, Attr.kind]

/-- A container option is pinned by its own constructor, whatever it contains. This is
    why the fixpoint's compatibility needs nothing from the recursive call — and why `opaque` is
    not a special construction. -/
theorem onKind_set (c : Codec) : Codec.OnKind ((setCodec c)) .set := by
  constructor <;> intro x hx <;> cases x <;>
    simp_all [setCodec, Value.kind, Attr.kind]

theorem onKind_array (c : Codec) :
    Codec.OnKind ((arrayCodec c)) .array := by
  constructor <;> intro x hx <;> cases x <;>
    simp_all [arrayCodec, Value.kind, Attr.kind]

theorem onKind_record (c : Codec) :
    Codec.OnKind ((recordCodec c)) .map := by
  refine ⟨fun v hv => ?_, fun a ha => ?_⟩
  · cases v
    case map keys f => rfl
    all_goals
      (simp only [recordCodec] at hv; exact absurd hv (by simp))
  · cases a
    case m keys g => rfl
    all_goals
      (simp only [recordCodec] at ha; exact absurd ha (by simp))

/-- The kinds `opaque`'s options are pinned to, in the order they are offered. -/
def opaqKinds : List Kind :=
  [.string, .boolean, .binary, .null, .number, .set, .array, .map]

/-- "The recursive union of everything self-identifying" (§3), spelled out: the eight
    options and the eight kinds that identify them. -/
theorem opaq_onKinds (c : Codec) :
    List.Forall₂ Codec.OnKind (opaqOptions c) opaqKinds :=
  .cons onKind_string (.cons onKind_boolean (.cons onKind_binary (.cons onKind_null
    (.cons onKind_number (.cons (onKind_set _) (.cons (onKind_array _)
      (.cons (onKind_record _) .nil)))))))

/-- Every option of `opaque` is lawful, given the recursive one is. -/
theorem lawful_opaqOptions {c : Codec} (hop : Lawful c) :
    ∀ o ∈ opaqOptions c, Lawful o := by
  intro o ho
  simp only [opaqOptions, List.mem_cons] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
  exacts [lawful_stringCodec, lawful_booleanCodec, lawful_binaryCodec,
    lawful_nullCodec, lawful_numberCodec, lawful_setCodec hop, lawful_arrayCodec hop,
    lawful_recordCodec hop, absurd h (by simp)]

/-- **Options pinned to distinct kinds are pairwise compatible**: each input has one kind, and
    one option answers to each kind. This is the compatibility of `opaque`'s options, and of the
    options of any recursive union whose options are kind-disjoint. -/
theorem compat_of_onKinds {os : List Codec} {ks : List Kind} (hl : ∀ o ∈ os, LawfulCore o)
    (hz : List.Forall₂ Codec.OnKind os ks) (hnd : ks.Nodup) :
    ∀ o ∈ os, ∀ o' ∈ os, Compat o o' := by
  have hp : List.Pairwise (fun S T => ∀ l, S l → ¬ T l) (ks.map (fun k l => l = k)) := by
    rw [List.pairwise_map]
    exact hnd.imp fun hne l hl hl' => hne (hl.symm.trans hl')
  refine compat_of_exclusive hl ?_ ?_
  · intro o ho v hv
    refine filter_eq_singleton_of_labels (adm := fun c v => (c.e v).isSome)
      (key := fun v => some v.kind) ?_ hp o ho hv
    rw [List.forall₂_map_right_iff]
    exact hz.imp fun _ _ h v hv => ⟨_, rfl, h.1 v hv⟩
  · intro o ho a ha
    refine filter_eq_singleton_of_labels (adm := fun c a => (c.p a).isSome)
      (key := fun a => some a.kind) ?_ hp o ho ha
    rw [List.forall₂_map_right_iff]
    exact hz.imp fun _ _ h a ha => ⟨_, rfl, h.2 a ha⟩

/-- `opaque`'s options are pairwise compatible: they are pinned to its eight kinds. -/
theorem compat_opaque (c : Codec) (hop : Lawful c) :
    ∀ o ∈ opaqOptions c, ∀ o' ∈ opaqOptions c, Compat o o' :=
  compat_of_onKinds (fun o ho => (lawful_opaqOptions hop o ho).core) (opaq_onKinds c) (by decide)

/-- One layer of `opaque` is lawful when the layer below is, with no bespoke induction: the sum
    lemma, its options' lemmas, and compatibility computed from the shapes — kinds partition the
    values, and the same kinds partition the attributes. -/
theorem lawful_opaqStep {c : Codec} (hop : Lawful c) : Lawful (opaqStep c) :=
  -- `μ` is `⊤`: the options name eight different members, so `unanimous` is `none`
  lawful_altCodec (lawful_opaqOptions hop) (compat_opaque c hop) (fun _ hm => nomatch hm)

end

end Calculus
