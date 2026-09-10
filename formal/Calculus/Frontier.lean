import Calculus.Lawful

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


/-- What each wire element reads back to: the value it came from. -/
theorem setImage_read {α β : Type} [DecidableEq β] {c : Codec} (h : LawfulCore c)
    {vinj : α → Value} {aout : Attr → Option β} {ainj : β → Attr}
    (hA : ∀ a b, aout a = some b → a = ainj b)
    {S : Finset α} {T : Finset β}
    (hI : setImage (fun x => (c.e (vinj x)).bind aout) S = some T) :
    ∀ y ∈ T, ∃ x ∈ S, c.p (ainj y) = some (vinj x) := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := (mem_setImage hI y).mp hy
  simp only [Option.bind_eq_some_iff] at hxy
  obtain ⟨a, hea, hoa⟩ := hxy
  rw [hA a y hoa] at hea
  exact ⟨x, hx, h.retract hea⟩

/-- `decSet` lands on the string branch when the reads produce strings. -/
theorem decSet_strBranch {α : Type} {c : Codec} {inj : α → Attr} {S : NEFinset α}
    {U : NEFinset String}
    (h1 : neSetImage (fun y => (c.p (inj y)).bind vStr) S = some U) :
    decSet c inj S = some (.strSet U) := by
  unfold decSet; rw [h1]

/-- …the numeric branch when they produce numbers, the string branch having failed. -/
theorem decSet_numBranch {α : Type} {c : Codec} {inj : α → Attr} {S : NEFinset α}
    {U : NEFinset Double}
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


/-- Core set: (R), (C) and (W). The `(set)` rule's member premise is what fixes which wire
    branch the write takes, so it is still a hypothesis — but nothing else is, and in
    particular no traversal and no non-emptiness side condition. -/
theorem lawfulCore_setCodec {c : Codec} {μ₀ μS : Member} (h : LawfulCore c)
    (hμ : c.μ = some μ₀) (hsm : setMember μ₀ = some μS) :
    LawfulCore (setCodec c) := by
  refine ⟨set_retract h, ?_, set_writes h⟩
  intro a t hp
  rcases setCodec_p_eq.mp hp with ⟨S, rfl, hD⟩ | ⟨S, rfl, hD⟩ | ⟨S, rfl, hD⟩ <;>
    · rcases decSet_mem hD with ⟨U, rfl, hm⟩ | ⟨U, rfl, hm⟩ | ⟨U, rfl, hm⟩ <;>
      · refine encSet_isSome_of h hsm (fun x y hxy => by injection hxy) ?_
          (fun x _ a' ha' => h.writes hμ ha')
        intro y hy
        obtain ⟨x, -, hpx⟩ := hm y hy
        exact h.canon hpx


/-! ### Which branch `encSet` takes

`encSet` tries `SS`, then `NS`, then `BS`. `lawfulCore_setCodec` only needed to know that
*some* branch fires; **(A)** needs to know *which*, because `Agree` pairs a wire set with a
wire set of the same family. The member of the elements' attributes decides it. -/

/-- Elements at member `S` take the `SS` branch. -/
theorem encSet_ss_of {α : Type} {c : Codec} {vinj : α → Value} {S : NEFinset α} {a : Attr}
    (hm : ∀ x ∈ S.1, ∀ b, c.e (vinj x) = some b → b.member = .S)
    (h : encSet c vinj S = some a) : ∃ T, a = .ss T := by
  obtain ⟨x₀, hx₀⟩ := S.2
  have hall := encSet_elem h
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hall x₀ hx₀)
  have hbm := hm x₀ hx₀ b hb
  unfold encSet at h
  cases hT : neSetImage (fun x => (c.e (vinj x)).bind sC.out) S with
  | some T => rw [hT] at h; exact ⟨T, (Option.some.inj h).symm⟩
  | none =>
    exfalso
    have hN : neSetImage (fun x => (c.e (vinj x)).bind nC.out) S = none :=
      neSetImage_none (setImage_none_of hx₀ (by cases b <;> simp_all [nC, Attr.member]))
    have hB : neSetImage (fun x => (c.e (vinj x)).bind bC.out) S = none :=
      neSetImage_none (setImage_none_of hx₀ (by cases b <;> simp_all [bC, Attr.member]))
    rw [hT, hN, hB] at h
    simp at h

/-- Elements at member `N` take the `NS` branch, the `SS` one having failed. -/
theorem encSet_ns_of {α : Type} {c : Codec} {vinj : α → Value} {S : NEFinset α} {a : Attr}
    (hm : ∀ x ∈ S.1, ∀ b, c.e (vinj x) = some b → b.member = .N)
    (h : encSet c vinj S = some a) : ∃ T, a = .ns T := by
  obtain ⟨x₀, hx₀⟩ := S.2
  have hall := encSet_elem h
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hall x₀ hx₀)
  have hbm := hm x₀ hx₀ b hb
  have hS : neSetImage (fun x => (c.e (vinj x)).bind sC.out) S = none :=
    neSetImage_none (setImage_none_of hx₀ (by cases b <;> simp_all [sC, Attr.member]))
  unfold encSet at h
  rw [hS] at h
  cases hT : neSetImage (fun x => (c.e (vinj x)).bind nC.out) S with
  | some T => rw [hT] at h; exact ⟨T, (Option.some.inj h).symm⟩
  | none =>
    exfalso
    have hB : neSetImage (fun x => (c.e (vinj x)).bind bC.out) S = none :=
      neSetImage_none (setImage_none_of hx₀ (by cases b <;> simp_all [bC, Attr.member]))
    rw [hT, hB] at h
    simp at h

/-- Elements at member `B` take the `BS` branch, both earlier ones having failed. -/
theorem encSet_bs_of {α : Type} {c : Codec} {vinj : α → Value} {S : NEFinset α} {a : Attr}
    (hm : ∀ x ∈ S.1, ∀ b, c.e (vinj x) = some b → b.member = .B)
    (h : encSet c vinj S = some a) : ∃ T, a = .bs T := by
  obtain ⟨x₀, hx₀⟩ := S.2
  have hall := encSet_elem h
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hall x₀ hx₀)
  have hbm := hm x₀ hx₀ b hb
  have hS : neSetImage (fun x => (c.e (vinj x)).bind sC.out) S = none :=
    neSetImage_none (setImage_none_of hx₀ (by cases b <;> simp_all [sC, Attr.member]))
  have hN : neSetImage (fun x => (c.e (vinj x)).bind nC.out) S = none :=
    neSetImage_none (setImage_none_of hx₀ (by cases b <;> simp_all [nC, Attr.member]))
  unfold encSet at h
  rw [hS, hN] at h
  obtain ⟨T, -, hTa⟩ := Option.map_eq_some_iff.mp h
  exact ⟨T, hTa.symm⟩


/-- **A set writes exactly when every element does.**

    Both directions, and neither needs a hypothesis the term does not already carry: the
    injectivity `encSet` demands comes from the element pair's own **(R)**
    (`encSet_isSome_of`), and every base's element map is injective for a reason —
    `Double.toDec` from `Double.roundtrip`, the other three by construction. This is why
    indexing `set` makes the value-side row exact where an arbitrary element term could not
    (a `held` adapter may collapse two elements). -/
theorem encSet_base_iff {α : Type} (b : SetBase) {vinj : α → Value}
    (hvi : ∀ x y, vinj x = vinj y → x = y) (S : NEFinset α) :
    (encSet b.elem vinj S).isSome = true ↔ ∀ x ∈ S.1, b.adm (vinj x) = true := by
  constructor
  · intro h x hx
    cases he : encSet b.elem vinj S with
    | none => rw [he] at h; exact nomatch h
    | some a => exact (b.adm_iff (vinj x)).mpr (encSet_elem he x hx)
  · intro h
    exact encSet_isSome_of (lawful_setBase b).core (b.setMember_elemMember) hvi
      (fun x hx => (b.adm_iff (vinj x)).mp (h x hx))
      (fun _ _ a' ha' => (lawful_setBase b).core.writes b.elem_μ ha')

/-- **`setCodec` is lawful**, and the argument is not `lawfulCore_setCodec` with `agree`
    bolted on. That theorem gets member uniformity from `c.μ`, and the two call sites in
    the `opaque` fixpoint cannot supply it: `opaqCodec`'s `μ` is `none`. Here it comes from
    **(A)** instead — a value read out of `Attr.s x` writes back to something that *agrees*
    with `Attr.s x`, hence shares its member — which is a fact about the attribute the read
    came from, not about the codec's index. -/
theorem lawful_setCodec {c : Codec} (h : Lawful c) : Lawful (setCodec c) := by
  refine ⟨set_retract h.core, ?_, set_writes h.core, ?_⟩
  · intro a t hp
    rcases setCodec_p_eq.mp hp with ⟨S, rfl, hD⟩ | ⟨S, rfl, hD⟩ | ⟨S, rfl, hD⟩
    · rcases decSet_mem hD with ⟨U, rfl, hm⟩ | ⟨U, rfl, hm⟩ | ⟨U, rfl, hm⟩ <;>
      · refine encSet_isSome_of (μ₀ := .S) (μS := .SS) h.core rfl
          (fun x y hxy => by injection hxy) ?_ ?_
        · intro y hy
          obtain ⟨x, -, hpx⟩ := hm y hy
          exact h.canon hpx
        · intro y hy a' ha'
          obtain ⟨x, -, hpx⟩ := hm y hy
          exact (h.agree hpx ha').member_eq
    · rcases decSet_mem hD with ⟨U, rfl, hm⟩ | ⟨U, rfl, hm⟩ | ⟨U, rfl, hm⟩ <;>
      · refine encSet_isSome_of (μ₀ := .N) (μS := .NS) h.core rfl
          (fun x y hxy => by injection hxy) ?_ ?_
        · intro y hy
          obtain ⟨x, -, hpx⟩ := hm y hy
          exact h.canon hpx
        · intro y hy a' ha'
          obtain ⟨x, -, hpx⟩ := hm y hy
          exact (h.agree hpx ha').member_eq
    · rcases decSet_mem hD with ⟨U, rfl, hm⟩ | ⟨U, rfl, hm⟩ | ⟨U, rfl, hm⟩ <;>
      · refine encSet_isSome_of (μ₀ := .B) (μS := .BS) h.core rfl
          (fun x y hxy => by injection hxy) ?_ ?_
        · intro y hy
          obtain ⟨x, -, hpx⟩ := hm y hy
          exact h.canon hpx
        · intro y hy a' ha'
          obtain ⟨x, -, hpx⟩ := hm y hy
          exact (h.agree hpx ha').member_eq
  · intro a t a' hp he
    rcases setCodec_p_eq.mp hp with ⟨S, rfl, hD⟩ | ⟨S, rfl, hD⟩ | ⟨S, rfl, hD⟩
    · rcases decSet_mem hD with ⟨U, rfl, hm⟩ | ⟨U, rfl, hm⟩ | ⟨U, rfl, hm⟩ <;>
      · obtain ⟨T, rfl⟩ := encSet_ss_of (fun y hy b hb => by
          obtain ⟨x, -, hpx⟩ := hm y hy
          exact (h.agree hpx hb).member_eq) he
        exact Agree.ss T S
    · rcases decSet_mem hD with ⟨U, rfl, hm⟩ | ⟨U, rfl, hm⟩ | ⟨U, rfl, hm⟩ <;>
      · obtain ⟨T, rfl⟩ := encSet_ns_of (fun y hy b hb => by
          obtain ⟨x, -, hpx⟩ := hm y hy
          exact (h.agree hpx hb).member_eq) he
        exact Agree.ns T S
    · rcases decSet_mem hD with ⟨U, rfl, hm⟩ | ⟨U, rfl, hm⟩ | ⟨U, rfl, hm⟩ <;>
      · obtain ⟨T, rfl⟩ := encSet_bs_of (fun y hy b hb => by
          obtain ⟨x, -, hpx⟩ := hm y hy
          exact (h.agree hpx hb).member_eq) he
        exact Agree.bs T S


/-! ### Keyed lookup and traversal facts (the keyed product consumes these) -/


/-- **What `fbNames` contains**: exactly the `fb` names the row omits.

    The list form needed a forty-line induction over the row; a `Finset.filter` needs
    `Finset.mem_filter`, and the four facts the object proofs use still fall out of it. -/
private theorem isFbB_eq {o : Option FieldSem} :
    isFbB o = true ↔ ∃ c v, o = some (.fb c v) := by
  cases o with
  | none => simp [isFbB]
  | some fs => cases fs <;> simp [isFbB]

theorem mem_fbNames {names : Finset Name} {sems : MapOf FieldSem} {k} :
    k ∈ fbNames names sems ↔ (∃ c v, sems.at k = some (.fb c v)) ∧ k ∉ names := by
  simp only [fbNames, Finset.mem_filter, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, isFbB_eq]
  exact ⟨fun ⟨_, hfb, hn⟩ => ⟨hfb, hn⟩,
         fun ⟨⟨c, v, hm⟩, hn⟩ => ⟨(MapOf.at_eq_some.mp hm).1, ⟨c, v, hm⟩, hn⟩⟩

theorem fbNames_mem {sems : MapOf FieldSem} {names : Finset Name} {k c v}
    (hm : sems.at k = some (.fb c v)) (hc : k ∉ names) : k ∈ fbNames names sems :=
  mem_fbNames.mpr ⟨⟨c, v, hm⟩, hc⟩

/-- Emptiness by `Finset.ext`, not by `Finset.eq_empty_of_forall_not_mem`: the mathlib
    lemma is proved classically, and this file's axiom base (`Axioms.lean`) does not
    admit `Classical.choice`. -/
theorem fbNames_empty {sems : MapOf FieldSem} {names : Finset Name}
    (h : ∀ k c v, sems.at k = some (.fb c v) → k ∈ names) : fbNames names sems = ∅ :=
  Finset.ext fun k =>
    ⟨fun hk => by obtain ⟨⟨c, v, hm⟩, hn⟩ := mem_fbNames.mp hk; exact absurd (h k c v hm) hn,
     fun hk => absurd hk (Finset.notMem_empty k)⟩

/-- The guard characterizations. One `decide` over the key set replaces the `List.all`,
    and the `Nodup` premise that used to accompany every use of them is gone. -/
theorem valPresentB_spec {sems : MapOf FieldSem} {names : Finset Name}
    (h : valPresentB sems names = true) {k fs} (hm : sems.at k = some fs)
    (hno : ∀ c, fs ≠ FieldSem.opt c) : k ∈ names := by
  obtain ⟨hk, rfl⟩ := MapOf.at_eq_some.mp hm
  have hb := of_decide_eq_true h ⟨k, hk⟩
  cases hs : sems.2 ⟨k, hk⟩ with
  | opt c => rw [hs] at hno; exact absurd rfl (hno c)
  | req c => rw [hs] at hb; exact of_decide_eq_true hb
  | fb c v => rw [hs] at hb; exact of_decide_eq_true hb

theorem valPresentB_of {sems : MapOf FieldSem} {names : Finset Name}
    (h : ∀ k fs, sems.at k = some fs → (∀ c, fs ≠ FieldSem.opt c) → k ∈ names) :
    valPresentB sems names = true := by
  refine decide_eq_true fun k => ?_
  cases hs : sems.2 k with
  | opt c => simp [valPresentAt]
  | req c =>
    simpa [valPresentAt, hs] using
      h k.1 (.req c) (by rw [MapOf.at_of_mem k, hs]) (fun _ h' => nomatch h')
  | fb c v =>
    simpa [valPresentAt, hs] using
      h k.1 (.fb c v) (by rw [MapOf.at_of_mem k, hs]) (fun _ h' => nomatch h')

theorem reqPresentB_spec {sems : MapOf FieldSem} {names : Finset Name}
    (h : reqPresentB sems names = true) {k c} (hm : sems.at k = some (.req c)) :
    k ∈ names := by
  obtain ⟨hk, hs⟩ := MapOf.at_eq_some.mp hm
  have hb := of_decide_eq_true h ⟨k, hk⟩
  rw [hs] at hb
  exact of_decide_eq_true hb

theorem reqPresentB_of {sems : MapOf FieldSem} {names : Finset Name}
    (h : ∀ k c, sems.at k = some (.req c) → k ∈ names) :
    reqPresentB sems names = true := by
  refine decide_eq_true fun k => ?_
  cases hs : sems.2 k with
  | req c => simpa [reqPresentAt, hs] using h k.1 c (by rw [MapOf.at_of_mem k, hs])
  | opt c => simp [reqPresentAt]
  | fb c v => simp [reqPresentAt]


/-! ### The keyed steps: round trip, definedness, agreement, and name preservation -/



/-! ### Carriers, continued: objects

    Placed here, after the name-dispatch helpers `p` needs. -/




/-- The same two, stated on the step the payload pair actually takes now: dispatch by
    name, then run that entry's codec. -/
theorem entry_domE' {sems : MapOf FieldSem} {rc? : Option Codec}
    (hs : ∀ k, Carrier (sems.2 k).codec) (hrc : ∀ c ∈ rc?, Carrier c)
    {k : Name} {v : Value} {a : Attr}
    (h : (entryCodec sems rc? k).bind (fun c => c.e v) = some a) :
    objEntryT sems rc? (k, v) := by
  cases hc : entryCodec sems rc? k with
  | none => rw [hc] at h; exact nomatch h
  | some c =>
    rw [hc] at h
    exact objEntryT_eq.mpr ⟨c, hc, (entryCodec_of hs hrc hc).domE h⟩

theorem entry_ranP' {sems : MapOf FieldSem} {rc? : Option Codec}
    (hs : ∀ k, Carrier (sems.2 k).codec) (hrc : ∀ c ∈ rc?, Carrier c)
    {k : Name} {a : Attr} {v : Value}
    (h : (entryCodec sems rc? k).bind (fun c => c.p a) = some v) :
    objEntryT sems rc? (k, v) := by
  cases hc : entryCodec sems rc? k with
  | none => rw [hc] at h; exact nomatch h
  | some c =>
    rw [hc] at h
    exact objEntryT_eq.mpr ⟨c, hc, (entryCodec_of hs hrc hc).ranP h⟩

/-- `fbValue` finds the stand-in a declared `fb` name reads to. -/
theorem fbValue_of {sems : MapOf FieldSem} {k c v}
 (hm : sems.at k = some (.fb c v)) :
    fbValue sems k = some v := by
  simp [fbValue, hm]

/-! #### The rest policy fixes both halves

`objectCodecCore` is stated over a free `rc? : Option Codec` and a free filter
`kn : Name → Bool` because that is what its payload pair takes. Nothing instantiates
them independently: the object rule reads both off one `rest : RestSem`, as `rcOf rest`
and `keepB rest sems`. The three lemmas here are what that costs, discharged once —
they used to be hypotheses on five signatures, and one of them was re-proved by hand at
the call site in `Soundness.lean`. -/

/-- A property of the rest policy's codec, from one per `rest = .codec c`. -/
theorem rcOf_forall {P : Codec → Prop} {rest : RestSem}
    (h : ∀ c, rest = .codec c → P c) : ∀ c ∈ rcOf rest, P c := by
  intro c hc
  cases rest with
  | codec c' =>
    replace hc : some c' = some c := hc
    cases hc
    exact h c rfl
  | drop => exact nomatch hc
  | refuse => exact nomatch hc

/-- What object-encode produces, `keepB` keeps: under `drop` an encoded entry's name
    is declared, and the other policies keep everything. -/
theorem keepB_of_entryWrite {sems : MapOf FieldSem} {rest : RestSem} :
    ∀ k v a, (entryCodec sems (rcOf rest) k).bind (fun c => c.e v) = some a →
      keepB rest sems k = true := by
  intro k v a h
  cases rest with
  | drop =>
    simp only [entryCodec] at h
    cases hsp : sems.at k with
    | none => rw [hsp] at h; simp only [rcOf, Option.bind_none] at h; exact nomatch h
    | some fs => simp [keepB, hsp]
  | refuse => rfl
  | codec rc => rfl

/-- Declared names pass every keep filter. -/
theorem keepB_of_declared {sems : MapOf FieldSem} {rest : RestSem} :
    ∀ k, (sems.at k).isSome = true → keepB rest sems k = true := by
  intro k h
  cases rest with
  | drop => exact h
  | refuse => rfl
  | codec rc => rfl

/-- §4's held set, both ways. The one premise past lawfulness is the doc's own: `hfb` is
    `(fallback)`'s `v(∗) ∈ dom(e)`, which with `domE` gives §4's `v : 𝟙 → T`. That the name
    filter never discards a declared name is not a premise but a fact about the policies —
    `keepB_of_declared`, discharged inline below, and true of all three.

    Writing is immediate. Reading has to account for the stand-ins: every non-`opt`
    name is present in the result — a `req` from the row it was stored in, an `fb`
    from the row or else from its stand-in — and every entry is on its set, the kept
    ones by `entry_ranP'`, the stand-ins by `hfb`. -/
theorem carrier_objectCodec {sems : MapOf FieldSem} {rest : RestSem}
    (hsems : ∀ k, Carrier (sems.2 k).codec)
    (hrc : ∀ rc, rcOf rest = some rc → Carrier rc)
    (hfb : ∀ k c v, sems.2 k = .fb c v → (c.e v).isSome) :
    Carrier (objectCodec sems rest) := by
  show Carrier (objectCodecCore sems (rcOf rest) (keepB rest sems))
  refine objectCodecCore_eq ▸ carrier_carried ?_ ?_
  · rintro p q h
    obtain ⟨hval, g, hg, rfl⟩ := objWrite_eq.mp h
    exact ⟨hval, fun k => entry_domE' hsems hrc (funImage_some hg k)⟩
  · rintro q p h
    obtain ⟨hreq, d, hd, rfl⟩ := objRead_eq.mp h
    constructor
    · refine valPresentB_of fun k fs hm hno => ?_
      have hkn : keepB rest sems k = true := keepB_of_declared k (by rw [hm]; rfl)
      rw [Finset.mem_union]
      cases fs with
      | opt c => exact absurd rfl (hno c)
      | req c =>
        exact Or.inl (Finset.mem_filter.mpr ⟨reqPresentB_spec hreq hm, by simpa using hkn⟩)
      | fb c v₀ =>
        by_cases hk : k ∈ q.1
        · exact Or.inl (Finset.mem_filter.mpr ⟨hk, by simpa using hkn⟩)
        · exact Or.inr (fbNames_mem hm hk)
    · intro k
      by_cases hk : k.1 ∈ q.1.filter (keepB rest sems ·)
      · simp only [dif_pos hk]
        exact entry_ranP' hsems hrc (funImage_some hd ⟨k.1, hk⟩)
      · simp only [dif_neg hk]
        have hfbm : k.1 ∈ fbNames q.1 sems :=
          (Finset.mem_union.mp k.2).resolve_left hk
        obtain ⟨⟨c, v₀, hm⟩, -⟩ := mem_fbNames.mp hfbm
        obtain ⟨hk', hs⟩ := MapOf.at_eq_some.mp hm
        rw [fbValue_of hm]
        refine objEntryT_eq.mpr ⟨c, ?_, ?_⟩
        · simp [entryCodec, hm, FieldSem.codec]
        · obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (hfb ⟨k.1, hk'⟩ c v₀ hs)
          exact (MapOf.at_forall (Q := fun fs => Carrier fs.codec) hsems hm).domE ha'





/-! #### §2's clauses for the object's payload pair

Each is proved once, from core children, and both `lawfulCore_objectCodec` and
`lawful_objectCodec` consume them. -/

section ObjectLaws
variable {sems : MapOf FieldSem} {rest : RestSem}

/-- (R): a written row is complete — every declared name present, none filtered out, no
    stand-in owed — so reading it back is the entrywise round trip and nothing else. -/
theorem object_retract (hf : ∀ k, LawfulCore (sems.2 k).codec)
    (hrc : ∀ c ∈ rcOf rest, LawfulCore c) :
    ∀ p q, objWrite sems (rcOf rest) p = some q →
      objRead sems (rcOf rest) (keepB rest sems) q = some p := by
  rintro p q h
  obtain ⟨hval, g, hg, rfl⟩ := objWrite_eq.mp h
  -- every name of a writable map is kept, so the `drop` filter is the identity
  have hfilter : p.1.filter (keepB rest sems ·) = p.1 :=
    Finset.filter_eq_self.mpr fun k hk => by
      simpa using keepB_of_entryWrite k (p.2 ⟨k, hk⟩) _ (funImage_some hg ⟨k, hk⟩)
  -- and no fallback name is missing, so nothing is adjoined
  have hfb0 : fbNames p.1 sems = ∅ :=
    fbNames_empty fun k c v hm => valPresentB_spec hval hm (fun _ h' => nomatch h')
  refine objRead_eq.mpr ⟨reqPresentB_of fun k c hm =>
    valPresentB_spec hval hm (fun _ h' => nomatch h'), ?_⟩
  refine ⟨fun k => p.2 ⟨k.1, (Finset.mem_filter.mp k.2).1⟩, funImage_eq fun k => ?_, ?_⟩
  · have hw := funImage_some hg ⟨k.1, (Finset.mem_filter.mp k.2).1⟩
    cases hc : entryCodec sems (rcOf rest) k.1 with
    | none => rw [hc] at hw; exact nomatch hw
    | some c =>
      simp only [hc, Option.bind_some] at hw ⊢
      exact (entryCodec_of hf hrc hc).retract hw
  · refine MapOf.ext ?_ ?_
    · simp only [hfilter, hfb0, Finset.union_empty]
    · intro k h₁ h₂
      have hk1 : k ∈ p.1.filter (keepB rest sems ·) := by rw [hfilter]; exact h₁
      simp only [dif_pos hk1]

/-- (C): what was read is writable again — the kept entries by (C) one level down, the
    stand-ins by `(fallback)`'s own premise `v(∗) ∈ dom(e)`. -/
theorem object_canon (hf : ∀ k, LawfulCore (sems.2 k).codec)
    (hrc : ∀ c ∈ rcOf rest, LawfulCore c)
    (hfb : ∀ k c v, sems.2 k = .fb c v → (c.e v).isSome = true) :
    ∀ q p, objRead sems (rcOf rest) (keepB rest sems) q = some p →
      (objWrite sems (rcOf rest) p).isSome = true := by
  rintro q p h
  obtain ⟨hreq, d, hd, rfl⟩ := objRead_eq.mp h
  have hval : valPresentB sems (q.1.filter (keepB rest sems ·) ∪ fbNames q.1 sems) = true := by
    refine valPresentB_of fun k fs hm hno => ?_
    have hknk : keepB rest sems k = true := keepB_of_declared k (by rw [hm]; rfl)
    rw [Finset.mem_union]
    by_cases hk : k ∈ q.1
    · exact Or.inl (Finset.mem_filter.mpr ⟨hk, by simpa using hknk⟩)
    · cases fs with
      | opt c => exact absurd rfl (hno c)
      | req c => exact absurd (reqPresentB_spec hreq hm) hk
      | fb c v => exact Or.inr (fbNames_mem hm hk)
  have hstep : ∀ k : {k // k ∈ q.1.filter (keepB rest sems ·) ∪ fbNames q.1 sems},
      ((entryCodec sems (rcOf rest) k.1).bind (fun c => c.e
        (if h : k.1 ∈ q.1.filter (keepB rest sems ·) then d ⟨k.1, h⟩
         else (fbValue sems k.1).getD .null))).isSome = true := by
    intro k
    by_cases hk : k.1 ∈ q.1.filter (keepB rest sems ·)
    · simp only [dif_pos hk]
      have hp := funImage_some hd ⟨k.1, hk⟩
      cases hc : entryCodec sems (rcOf rest) k.1 with
      | none => rw [hc] at hp; exact nomatch hp
      | some c =>
        simp only [hc, Option.bind_some] at hp ⊢
        exact (entryCodec_of hf hrc hc).canon hp
    · simp only [dif_neg hk]
      obtain ⟨⟨c, v₀, hm⟩, -⟩ :=
        mem_fbNames.mp ((Finset.mem_union.mp k.2).resolve_left hk)
      have hc : entryCodec sems (rcOf rest) k.1 = some c := by
        simp [entryCodec, hm, FieldSem.codec]
      obtain ⟨hk', hs⟩ := MapOf.at_eq_some.mp hm
      simp only [fbValue_of hm, hc, Option.bind_some, Option.getD_some]
      exact hfb ⟨k.1, hk'⟩ c v₀ hs
  simp only [objWrite, if_pos hval]
  exact funImage_map_isSome (funImage_isSome hstep) _

theorem object_agree (hf : ∀ k, Lawful (sems.2 k).codec)
    (hrc : ∀ c ∈ rcOf rest, Lawful c) :
    ∀ q p q', objRead sems (rcOf rest) (keepB rest sems) q = some p →
      objWrite sems (rcOf rest) p = some q' → Agree (mA.into q') (mA.into q) := by
  rintro q p q' hD hE
  obtain ⟨hreq, d, hd, rfl⟩ := objRead_eq.mp hD
  obtain ⟨hval, g, hg, rfl⟩ := objWrite_eq.mp hE
  refine Agree.m _ _ _ _ fun k hx hy => ?_
  -- a name the stored item carries cannot be one the row omits, so the `fb` half of the
  -- union is unreachable here and only the kept entries have to agree
  have hkf : k ∈ q.1.filter (keepB rest sems ·) :=
    (Finset.mem_union.mp hx).resolve_right fun h => (mem_fbNames.mp h).2 hy
  have hp := funImage_some hd ⟨k, hkf⟩
  have hw := funImage_some hg ⟨k, hx⟩
  cases hc : entryCodec sems (rcOf rest) k with
  | none => rw [hc] at hp; exact nomatch hp
  | some c =>
    simp only [hc, Option.bind_some] at hp hw
    simp only [dif_pos hkf] at hw
    exact (entryCodec_of hf hrc hc).agree hp hw

end ObjectLaws

/-- The keyed product — the doc's `object`. `hfb` is §4's `v(∗) ∈ dom(e)`. -/
theorem lawful_objectCodec {sems : MapOf FieldSem} {rest : RestSem}
    (hf : ∀ k, Lawful (sems.2 k).codec)
    (hfb : ∀ k c v, sems.2 k = .fb c v → (c.e v).isSome)
    (hrest : ∀ c, rest = .codec c → Lawful c) :
    Lawful (objectCodec sems rest) := by
  show Lawful (objectCodecCore sems (rcOf rest) (keepB rest sems))
  have hf' := fun k => (hf k).core
  have hrc' := fun c hc => ((rcOf_forall hrest) c hc).core
  exact objectCodecCore_eq ▸ lawful_carried (fun _ => rfl)
    (object_retract hf' hrc') (object_canon hf' hrc' hfb)
    (object_agree hf (rcOf_forall hrest))

theorem lawfulCore_objectCodec {sems : MapOf FieldSem} {rest : RestSem}
    (hf : ∀ k, LawfulCore (sems.2 k).codec)
    (hfb : ∀ k c v, sems.2 k = .fb c v → (c.e v).isSome)
    (hrest : ∀ c, rest = .codec c → LawfulCore c) :
    LawfulCore (objectCodec sems rest) := by
  show LawfulCore (objectCodecCore sems (rcOf rest) (keepB rest sems))
  exact objectCodecCore_eq ▸ lawfulCore_carried (fun _ => rfl)
    (object_retract hf (rcOf_forall hrest)) (object_canon hf (rcOf_forall hrest) hfb)

/-- The sum's core laws. (U) is what makes them hold: it says the option that wrote is
    the only one admitting either side of the pair, so the round trip comes back through
    the same option it went out through. -/
theorem lawfulCore_altCodec {os : List OptionSem} {μA : Option Member}
    (h : ∀ o ∈ os, LawfulCore o.c) (hU : UniqueBothWays os)
    (hW : ∀ m, μA = some m → ∀ o ∈ os, ∀ t a, o.c.e t = some a → a.member = m) :
    LawfulCore (altCodec os μA) where
  retract he := by
    obtain ⟨o, hf, hoe⟩ := altCodec_e.mp he
    have ho := (mem_of_filter_eq_singleton hf).1
    exact altCodec_p.mpr ⟨o, hU.1 o ho _ _ hf hoe, (h o ho).retract hoe⟩
  canon hp := by
    obtain ⟨o, hf, hop⟩ := altCodec_p.mp hp
    have ho := (mem_of_filter_eq_singleton hf).1
    obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp ((h o ho).canon hop)
    exact Option.isSome_iff_exists.mpr
      ⟨a', altCodec_e.mpr ⟨o, hU.2 o ho _ _ _ hf hop ha', ha'⟩⟩
  writes := by
    intro μ hμ t a he
    obtain ⟨o, hf, hoe⟩ := altCodec_e.mp he
    exact hW μ hμ o (mem_of_filter_eq_singleton hf).1 t a hoe

/-- …and (MP) with them: the option that read is the option that re-writes, again by
    (U), so `≼` at the union is `≼` at that one option. -/
theorem lawful_altCodec {os : List OptionSem} {μA : Option Member}
    (h : ∀ o ∈ os, Lawful o.c) (hU : UniqueBothWays os)
    (hW : ∀ m, μA = some m → ∀ o ∈ os, ∀ t a, o.c.e t = some a → a.member = m) :
    Lawful (altCodec os μA) :=
  { lawfulCore_altCodec (fun o ho => (h o ho).core) hU hW with
    agree := by
      intro a t a' hp he
      obtain ⟨o, hf, hop⟩ := altCodec_p.mp hp
      have ho := (mem_of_filter_eq_singleton hf).1
      obtain ⟨a'', ha''⟩ := Option.isSome_iff_exists.mp ((h o ho).canon hop)
      have hV := hU.2 o ho _ _ _ hf hop ha''
      obtain ⟨o', hf', hoe⟩ := altCodec_e.mp he
      have hoo : o' = o := by simpa using hf'.symm.trans hV
      subst hoo
      exact (h _ ho).agree hop hoe }


/-! ### (U) by kind, and `opaque`'s fixpoint

    §5's other disjointness discharger, and the one `(opaque)` needs. An option is
    *pinned to a kind* when it admits only values and attributes of that kind — which is
    precisely what §3 means by calling `opaque`'s options "self-identifying". Pin each
    option and keep the kinds distinct, and (U) follows with nothing said about what the
    options contain: `onKind_set` and its two neighbours hold for *any* element codec,
    which is why the fixpoint's unique admission needs nothing from the recursive call. -/

/-- An option pinned to a kind: it admits only values and attributes of that kind. -/
def OptionSem.OnKind (o : OptionSem) (k : Kind) : Prop :=
  (∀ v, o.admitV v = true → v.kind = k) ∧ (∀ a, o.admitA a = true → a.kind = k)

/-- **(U) by disjoint admissibility** — the structure the rest of this section presents.

    Give each option a set of values and a set of attributes it is allowed to admit, and
    keep each family pairwise disjoint: then no input reaches two options, and admission is
    unique. That is the entire separation argument. Kinds, members, tags and admissible
    sets are *ways of building* those two families, not four different conditions — and
    the two families are independent, which is what lets the value side be separated by a
    kind while the attribute side is separated by a member. -/
theorem uniqueAdmission_of_disjoint {os : List OptionSem}
    {SVs : List (Value → Prop)} {SAs : List (Attr → Prop)}
    (hV : List.Forall₂ (fun o S => ∀ v, o.admitV v = true → S v) os SVs)
    (hA : List.Forall₂ (fun o S => ∀ a, o.admitA a = true → S a) os SAs)
    (hdV : List.Pairwise (fun S T => ∀ v, S v → ¬ T v) SVs)
    (hdA : List.Pairwise (fun S T => ∀ a, S a → ¬ T a) SAs)
    (hw : ∀ o ∈ os, ∀ t a, o.c.e t = some a → o.admitV t = true ∧ o.admitA a = true) :
    UniqueAdmission os := fun o ho t a he =>
  ⟨filter_eq_singleton_of_disjoint hA hdA o ho (hw o ho t a he).2,
   filter_eq_singleton_of_disjoint hV hdV o ho (hw o ho t a he).1⟩

theorem uniqueAdmission_of_sharedBase {base : Codec} {cs : List Codec}
    {qs : List (Value → Bool)} (hlaw : LawfulCore base)
    (hz : List.Forall₂ (fun ci q => ci.e = (base.restrict q).e ∧ ci.p = (base.restrict q).p) cs qs)
    (hdisj : List.Pairwise (fun q q' => ∀ v, q v = true → q' v = false) qs) :
    UniqueAdmission (cs.map OptionSem.byAttempt) := by
  refine uniqueAdmission_of_disjoint
    (SVs := qs.map (fun q v => q v = true))
    (SAs := qs.map (fun q a => ∃ v, base.p a = some v ∧ q v = true)) ?_ ?_ ?_ ?_ ?_
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine hz.imp fun ci q h v hv => ?_
    have : ((base.restrict q).e v).isSome = true := h.1 ▸ hv
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp this
    exact (restrict_e.mp hw).1
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine hz.imp fun ci q h a ha => ?_
    have : ((base.restrict q).p a).isSome = true := h.2 ▸ ha
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp this
    obtain ⟨hp, hq⟩ := restrict_p.mp hw
    exact ⟨w, hp, hq⟩
  · rw [List.pairwise_map]
    refine hdisj.imp fun h v hv hv' => ?_
    simp only at hv hv'; rw [h v hv] at hv'; exact nomatch hv'
  · rw [List.pairwise_map]
    refine hdisj.imp fun h a hx hy => ?_
    obtain ⟨v, hv, hqv⟩ := hx
    obtain ⟨v', hv', hqv'⟩ := hy
    rw [hv] at hv'; cases hv'
    rw [h v hqv] at hqv'; exact nomatch hqv'
  · refine List.forall_mem_map.mpr fun ci hci t a he => ?_
    obtain ⟨q, -, hq⟩ := hz.mem_left hci
    have he' : (base.restrict q).e t = some a := hq.1 ▸ he
    obtain ⟨hqt, hb⟩ := restrict_e.mp he'
    refine ⟨?_, ?_⟩
    · show (ci.e t).isSome = true
      rw [hq.1, he']; rfl
    · show (ci.p a).isSome = true
      rw [hq.2, restrict_p.mpr ⟨hlaw.retract hb, hqt⟩]; rfl

/-- An option pinned to a **set of labels**, under a partial projection of each side of
    the pair. `OnKind` is the singleton case at `Value.kind`/`Attr.kind`; `(dunion)`'s
    tag sets are the general one at `tagOfV`/`tagOfA`. -/
def OptionSem.Labelled {L : Type} (πV : Value → Option L) (πA : Attr → Option L)
    (o : OptionSem) (S : L → Prop) : Prop :=
  (∀ v, o.admitV v = true → ∃ l, πV v = some l ∧ S l) ∧
  (∀ a, o.admitA a = true → ∃ l, πA a = some l ∧ S l)

/-- **(U) by projection** — §5's two outright dischargers, once.

    Label each side of the pair by a partial projection of the input, give each option the
    set of labels it answers to, and keep those sets pairwise disjoint: then no input can
    reach two options, because the label it carries is a property of the *input* and lands
    in at most one option's set. `hw` is the only codec-facing premise, and it is what
    ties a canonical pair to its own option's admission.

    Kind-separation (`opaque`'s fixpoint) and tag-separation (`(dunion)`) are this theorem
    at two projections; §5's table reads as four conditions and is one. -/
theorem uniqueAdmission_of_labels {L : Type} {πV : Value → Option L} {πA : Attr → Option L}
    {os : List OptionSem} {Ss : List (L → Prop)}
    (hz : List.Forall₂ (OptionSem.Labelled πV πA) os Ss)
    (hdisj : List.Pairwise (fun S T => ∀ l, S l → ¬ T l) Ss)
    (hw : ∀ o ∈ os, ∀ t a, o.c.e t = some a → o.admitV t = true ∧ o.admitA a = true) :
    UniqueAdmission os := fun o ho t a he =>
  ⟨filter_eq_singleton_of_labels (hz.imp fun _ _ h => h.2) hdisj o ho (hw o ho t a he).2,
   filter_eq_singleton_of_labels (hz.imp fun _ _ h => h.1) hdisj o ho (hw o ho t a he).1⟩
-- `uniqueAdmission_of_labels` is `uniqueAdmission_of_disjoint` with both families pulled
-- back along one projection; sharing the label type `L` is a convenience of the two cases
-- that need it (a tag, a kind), not part of the structure.

/-- **(U) by kind-separation**, `uniqueAdmission_of_labels` at the total projection
    `Value.kind`/`Attr.kind` with one label per option: `Nodup` is disjointness of
    singletons. -/
theorem uniqueAdmission_of_kinds {os : List OptionSem} {ks : List Kind}
    (hz : List.Forall₂ OptionSem.OnKind os ks) (hnd : ks.Nodup)
    (hw : ∀ o ∈ os, ∀ t a, o.c.e t = some a →
      o.admitV t = true ∧ o.admitA a = true) :
    UniqueAdmission os := by
  refine uniqueAdmission_of_labels (πV := fun v => some v.kind) (πA := fun a => some a.kind)
    (Ss := ks.map (fun k l => l = k)) ?_ ?_ hw
  · rw [List.forall₂_map_right_iff]
    exact hz.imp fun _ _ h =>
      ⟨fun v hv => ⟨_, rfl, h.1 v hv⟩, fun a ha => ⟨_, rfl, h.2 a ha⟩⟩
  · rw [List.pairwise_map]
    exact hnd.imp fun hne l hl hl' => hne (hl.symm.trans hl')

/-- An option that decides by attempting admits what it writes, on both sides — the
    read side by (R), which is the only thing `hw` above ever needs. -/
theorem byAttempt_write {c : Codec} (h : Lawful c) {t a} (he : c.e t = some a) :
    (OptionSem.byAttempt c).admitV t = true ∧ (OptionSem.byAttempt c).admitA a = true :=
  ⟨by simp [OptionSem.byAttempt, he], by simp [OptionSem.byAttempt, h.retract he]⟩

/-! ### `(dunion)` as a lookup

A discriminated union is a **lookup**, and the list of tag-labelled options is that lookup with
its key set spread over a list and its uniqueness left as an obligation. A `MapOf Codec` is the
same thing with the key set as a key set, and it changes what has to be proved rather than how.

**`hdisj` goes and the whole uniqueness chain goes with it.** ~~uniqueAdmission_byTag~~,
`uniqueBothWays_of_uniqueAdmission` at this site, ~~labelled_byTag~~ and ~~OptionSem.byTag~~ existed to
establish that at most one option answers to a tag. A key set says it, so there is nothing left
to discharge: `lawful_dunionTable` below takes two premises where ~~lawful_dunionCodec~~ took three.

**`hstamp` stays, per key, and it is what makes the lookup lawful at all.** `e` routes through
`tagOfV` and `p` routes through `tagOfA`, so the two halves reach the same variant only if that
variant writes its own tag onto the attribute it produces. Without it the codec would encode
through one key and decode through another. It is the semantic twin of the coherence premise the
term carries, and `dunion_stamp` is what supplies it. -/

/-- The stamp a lookup needs, keyed rather than listed: every variant writes its own key, on both
    halves of every pair it produces. -/
def StampedAt (d : Name) (m : MapOf Codec) : Prop :=
  ∀ (k : {k // k ∈ m.1}) v a, (m.2 k).e v = some a →
    tagOfA d a = some k.1 ∧ tagOfV d v = some k.1

/-- §5 `(dunion)`, as the lookup it is: read the tag, index the table, run that one variant.

    No `altCodec`, no filtered list, and no enumeration of the key set — which is the point, since
    enumerating a `Finset` is `Finset.toList` and that reaches `Classical.choice`. The two readers
    are the ones a decimal tag widened, so this works at `string` and `decimal` alike. -/
def dunionTable (d : Name) (m : MapOf Codec) : Codec :=
  -- **`T` is the disjunction over the key set and says nothing about the tag.** The sharper
  -- reading — "the value's own tag picks the variant" — is true and costs two premises on
  -- `Carrier`: `ranP` gives a value from the *attribute*'s key, and recovering the *value*'s key
  -- needs (C) and the stamp. `T` is an upper bound that `Carrier` keeps `e` and `p` inside, so
  -- the looser one is the right one, and the fact stays where it is used rather than declared.
  { T := fun v => ∃ k : {k // k ∈ m.1}, (m.2 k).T v
    μ := some .M
    e := fun v => match tagOfV d v with
      | some tag => if h : tag ∈ m.1 then (m.2 ⟨tag, h⟩).e v else none
      | none => none
    p := fun a => match tagOfA d a with
      | some tag => if h : tag ∈ m.1 then (m.2 ⟨tag, h⟩).p a else none
      | none => none }

/-- The write half, as the rewrite every proof over it names rather than unfolding. -/
theorem dunionTable_e {d : Name} {m : MapOf Codec} {v : Value} {a : Attr} :
    (dunionTable d m).e v = some a ↔
      ∃ (tag : String) (h : tag ∈ m.1),
        tagOfV d v = some tag ∧ (m.2 ⟨tag, h⟩).e v = some a := by
  show (match tagOfV d v with
        | some tag => if h : tag ∈ m.1 then (m.2 ⟨tag, h⟩).e v else none
        | none => none) = some a ↔ _
  cases htv : tagOfV d v with
  | none => exact Iff.intro (fun he => nomatch he) (fun ⟨_, _, ht, _⟩ => nomatch ht)
  | some tag =>
    show (if h : tag ∈ m.1 then (m.2 ⟨tag, h⟩).e v else none) = some a ↔ _
    by_cases hk : tag ∈ m.1
    · rw [dif_pos hk]
      refine Iff.intro (fun he => ⟨tag, hk, rfl, he⟩) ?_
      rintro ⟨tag', hk', ht, he⟩
      obtain rfl : tag' = tag := (Option.some.inj ht).symm
      exact he
    · rw [dif_neg hk]
      refine Iff.intro (fun he => nomatch he) ?_
      rintro ⟨tag', hk', ht, -⟩
      obtain rfl : tag' = tag := (Option.some.inj ht).symm
      exact absurd hk' hk

/-- …and the read half. -/
theorem dunionTable_p {d : Name} {m : MapOf Codec} {a : Attr} {v : Value} :
    (dunionTable d m).p a = some v ↔
      ∃ (tag : String) (h : tag ∈ m.1),
        tagOfA d a = some tag ∧ (m.2 ⟨tag, h⟩).p a = some v := by
  show (match tagOfA d a with
        | some tag => if h : tag ∈ m.1 then (m.2 ⟨tag, h⟩).p a else none
        | none => none) = some v ↔ _
  cases hta : tagOfA d a with
  | none => exact Iff.intro (fun hp => nomatch hp) (fun ⟨_, _, ht, _⟩ => nomatch ht)
  | some tag =>
    show (if h : tag ∈ m.1 then (m.2 ⟨tag, h⟩).p a else none) = some v ↔ _
    by_cases hk : tag ∈ m.1
    · rw [dif_pos hk]
      refine Iff.intro (fun hp => ⟨tag, hk, rfl, hp⟩) ?_
      rintro ⟨tag', hk', ht, hp⟩
      obtain rfl : tag' = tag := (Option.some.inj ht).symm
      exact hp
    · rw [dif_neg hk]
      refine Iff.intro (fun hp => nomatch hp) ?_
      rintro ⟨tag', hk', ht, -⟩
      obtain rfl : tag' = tag := (Option.some.inj ht).symm
      exact absurd hk' hk

/-- **Two premises, where the list form takes three.** The variants' own laws and the stamp; the
    disjointness premise has nowhere to go, because the key set is where it went. -/
theorem lawful_dunionTable {d : Name} {m : MapOf Codec}
    (h : ∀ k, Lawful (m.2 k)) (hstamp : StampedAt d m) :
    Lawful (dunionTable d m) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v a he
    obtain ⟨tag, hk, htv, hve⟩ := dunionTable_e.mp he
    obtain ⟨hA, -⟩ := hstamp ⟨tag, hk⟩ v a hve
    exact dunionTable_p.mpr ⟨tag, hk, hA, (h ⟨tag, hk⟩).retract hve⟩
  · intro a v hp
    obtain ⟨tag, hk, hta, hvp⟩ := dunionTable_p.mp hp
    obtain ⟨a', hae⟩ := Option.isSome_iff_exists.mp ((h ⟨tag, hk⟩).canon hvp)
    obtain ⟨-, hV⟩ := hstamp ⟨tag, hk⟩ v a' hae
    exact Option.isSome_iff_exists.mpr ⟨a', dunionTable_e.mpr ⟨tag, hk, hV, hae⟩⟩
  · rintro μ hμ v a he
    cases hμ
    obtain ⟨tag, hk, -, hve⟩ := dunionTable_e.mp he
    obtain ⟨hA, -⟩ := hstamp ⟨tag, hk⟩ v a hve
    -- only an `M` carries a tag at all, so the stamp fixes the member
    cases a <;> simp only [tagOfA] at hA <;> first | rfl | exact nomatch hA
  · intro a v a' hp he
    obtain ⟨tag, hk, hta, hvp⟩ := dunionTable_p.mp hp
    obtain ⟨tag', hk', htv, hve⟩ := dunionTable_e.mp he
    -- **the value carries one tag**, so the write half lands on the key the read half came from:
    -- the variant the read half chose writes *something* by (C), and the stamp says that
    -- something carries the read half's key
    obtain ⟨a'', hae⟩ := Option.isSome_iff_exists.mp ((h ⟨tag, hk⟩).canon hvp)
    obtain ⟨-, hV⟩ := hstamp ⟨tag, hk⟩ v a'' hae
    obtain rfl : tag' = tag := by rw [hV] at htv; exact (Option.some.inj htv).symm
    exact (h ⟨_, hk⟩).agree hvp hve

/-- **On its carrier from the variants' alone**, one premise, as `altCodec` takes one. `T` is the
    disjunction over the key set, so a value either half produces sits under the key it came
    from — and neither half has to know it is the *same* key, which is what dropping the tag
    conjunct from `T` bought. -/
theorem carrier_dunionTable {d : Name} {m : MapOf Codec}
    (h : ∀ k, Carrier (m.2 k)) : Carrier (dunionTable d m) := by
  refine ⟨?_, ?_⟩
  · intro v a he
    obtain ⟨tag, hk, -, hve⟩ := dunionTable_e.mp he
    exact ⟨⟨tag, hk⟩, (h ⟨tag, hk⟩).domE hve⟩
  · intro a v hp
    obtain ⟨tag, hk, -, hvp⟩ := dunionTable_p.mp hp
    exact ⟨⟨tag, hk⟩, (h ⟨tag, hk⟩).ranP hvp⟩

/-- Core `(dunion)`: the same two premises, with core variants. -/
theorem lawfulCore_dunionTable {d : Name} {m : MapOf Codec}
    (h : ∀ k, LawfulCore (m.2 k)) (hstamp : StampedAt d m) :
    LawfulCore (dunionTable d m) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v a he
    obtain ⟨tag, hk, htv, hve⟩ := dunionTable_e.mp he
    obtain ⟨hA, -⟩ := hstamp ⟨tag, hk⟩ v a hve
    exact dunionTable_p.mpr ⟨tag, hk, hA, (h ⟨tag, hk⟩).retract hve⟩
  · intro a v hp
    obtain ⟨tag, hk, hta, hvp⟩ := dunionTable_p.mp hp
    obtain ⟨a', hae⟩ := Option.isSome_iff_exists.mp ((h ⟨tag, hk⟩).canon hvp)
    obtain ⟨-, hV⟩ := hstamp ⟨tag, hk⟩ v a' hae
    exact Option.isSome_iff_exists.mpr ⟨a', dunionTable_e.mpr ⟨tag, hk, hV, hae⟩⟩
  · rintro μ hμ v a he
    cases hμ
    obtain ⟨tag, hk, -, hve⟩ := dunionTable_e.mp he
    obtain ⟨hA, -⟩ := hstamp ⟨tag, hk⟩ v a hve
    cases a <;> simp only [tagOfA] at hA <;> first | rfl | exact nomatch hA

/-! ### `opaque`'s options, each pinned to its kind -/

theorem onKind_string : OptionSem.OnKind (.byAttempt stringCodec) .string := by
  constructor <;> intro x hx <;> cases x <;>
    simp_all [OptionSem.byAttempt, stringCodec, Value.kind, Attr.kind]

theorem onKind_boolean : OptionSem.OnKind (.byAttempt booleanCodec) .boolean := by
  constructor <;> intro x hx <;> cases x <;>
    simp_all [OptionSem.byAttempt, booleanCodec, Value.kind, Attr.kind]

theorem onKind_binary : OptionSem.OnKind (.byAttempt binaryCodec) .binary := by
  constructor <;> intro x hx <;> cases x <;>
    simp_all [OptionSem.byAttempt, binaryCodec, Value.kind, Attr.kind]

theorem onKind_null : OptionSem.OnKind (.byAttempt nullCodec) .null := by
  constructor <;> intro x hx <;> cases x <;>
    simp_all [OptionSem.byAttempt, nullCodec, Value.kind, Attr.kind]

/-- The `Numbers` policy: `lossy` offers the number option, `refuse` offers the empty
    one — which admits nothing, so the pinning holds either way. -/
theorem onKind_number (lossy : Bool) :
    OptionSem.OnKind (.byAttempt (if lossy then numberCodec else Codec.empty)) .number := by
  cases lossy <;> constructor <;> intro x hx <;> cases x <;>
    simp_all [OptionSem.byAttempt, numberCodec, Codec.empty, Value.kind, Attr.kind]

/-- A container option is pinned by its own constructor, whatever it contains. This is
    why the fixpoint's (U) needs nothing from the recursive call — and why `opaque` is
    not a special construction. -/
theorem onKind_set (c : Codec) : OptionSem.OnKind (.byAttempt (setCodec c)) .set := by
  constructor <;> intro x hx <;> cases x <;>
    simp_all [OptionSem.byAttempt, setCodec, Value.kind, Attr.kind]

theorem onKind_array (c : Codec) :
    OptionSem.OnKind (.byAttempt (arrayCodec c)) .array := by
  constructor <;> intro x hx <;> cases x <;>
    simp_all [OptionSem.byAttempt, arrayCodec, Value.kind, Attr.kind]

theorem onKind_record (c : Codec) :
    OptionSem.OnKind (.byAttempt (recordCodec c)) .map := by
  refine ⟨fun v hv => ?_, fun a ha => ?_⟩
  · cases v
    case map keys f => rfl
    all_goals
      (simp only [OptionSem.byAttempt, recordCodec] at hv; exact absurd hv (by simp))
  · cases a
    case m keys g => rfl
    all_goals
      (simp only [OptionSem.byAttempt, recordCodec] at ha; exact absurd ha (by simp))

/-- The kinds `opaque`'s options are pinned to, in the order they are offered. -/
def opaqKinds : List Kind :=
  [.string, .boolean, .binary, .null, .number, .set, .array, .map]

/-- "The recursive union of everything self-identifying" (§3), spelled out: the eight
    options and the eight kinds that identify them. -/
theorem opaq_onKinds (fuel : Nat) (lossy : Bool) :
    List.Forall₂ OptionSem.OnKind (opaqOptions lossy (opaqCodec fuel lossy)) opaqKinds :=
  .cons onKind_string (.cons onKind_boolean (.cons onKind_binary (.cons onKind_null
    (.cons (onKind_number lossy) (.cons (onKind_set _) (.cons (onKind_array _)
      (.cons (onKind_record _) .nil)))))))

/-- The `Numbers` option, lawful either way: `numberCodec` when `lossy`, and the empty
    codec — the absence of an option — when `refuse`. -/
theorem lawful_numOption (lossy : Bool) :
    Lawful (if lossy then numberCodec else Codec.empty) := by
  cases lossy
  · exact Lawful.empty
  · exact lawful_numberCodec

/-- Every option of `opaque` is lawful, given the recursive one is. -/
theorem lawful_opaqOptions {fuel : Nat} {lossy : Bool}
    (hop : Lawful (opaqCodec fuel lossy)) :
    ∀ o ∈ opaqOptions lossy (opaqCodec fuel lossy), Lawful o.c := by
  intro o ho
  simp only [opaqOptions, List.mem_cons] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
  exacts [lawful_stringCodec, lawful_booleanCodec, lawful_binaryCodec,
    lawful_nullCodec, lawful_numOption lossy, lawful_setCodec hop, lawful_arrayCodec hop,
    lawful_recordCodec hop, absurd h (by simp)]

/-- **(U) for `opaque`**, the fourth row of §5's discharger table: the eight options are
    pinned to eight distinct kinds, and each admits what it writes, so admission is
    unique on both sides. The only premise is the recursive option's lawfulness, which
    `uAtCan_opaque` (`Discharge.lean`) discharges. -/
theorem uniqueAdmission_opaque (fuel : Nat) (lossy : Bool)
    (hop : Lawful (opaqCodec fuel lossy)) :
    UniqueAdmission (opaqOptions lossy (opaqCodec fuel lossy)) := by
  refine uniqueAdmission_of_kinds (opaq_onKinds fuel lossy) (by decide) ?_
  intro o ho t a he
  simp only [opaqOptions, List.mem_cons] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
  exacts [byAttempt_write lawful_stringCodec he,
    byAttempt_write lawful_booleanCodec he, byAttempt_write lawful_binaryCodec he,
    byAttempt_write lawful_nullCodec he, byAttempt_write (lawful_numOption lossy) he,
    byAttempt_write (lawful_setCodec hop) he,
    byAttempt_write (lawful_arrayCodec hop) he,
    byAttempt_write (lawful_recordCodec hop) he, absurd h (by simp)]

/-- `opaque` closes with no bespoke induction: the sum lemma, its options' lemmas, and
    unique admission computed from the shapes — kinds partition the values, and the same
    kinds partition the attributes. -/
theorem lawful_opaqCodec : ∀ (fuel : Nat) (lossy : Bool), Lawful (opaqCodec fuel lossy)
  | 0, _ => Lawful.empty
  | fuel+1, lossy =>
    -- `μ` is `⊤`: the options name eight different members, so `unanimous` is `none`
    have hop : Lawful (opaqCodec fuel lossy) := lawful_opaqCodec fuel lossy
    lawful_altCodec (lawful_opaqOptions hop)
      (uniqueBothWays_of_uniqueAdmission (uniqueAdmission_opaque fuel lossy hop))
      (fun _ hm => nomatch hm)

end

end Calculus
