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
    the host's decimal spelling from the host's round trip, the other three by construction. This is why
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

theorem valPresentB_of {sems : MapOf FieldSem} {names : Finset Name}
    (h : ∀ k fs, sems.at k = some fs → (∀ c, fs ≠ FieldSem.opt c) → k ∈ names) :
    valPresentB sems names = true := by
  refine decide_eq_true fun k => ?_
  cases hs : sems.2 k with
  | opt c => simp [valPresentAt]
  | req c =>
    simpa [valPresentAt, hs] using
      h k.1 (.req c) (by rw [MapOf.at_of_mem k, hs]) (fun _ h' => nomatch h')

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

/-- §4's held set follows from the entry carriers. The current-schema reader returns only stored
    entries, so the object row needs no extra reader premise. -/
theorem carrier_objectCodec {sems : MapOf FieldSem} {rest : RestSem}
    (hsems : ∀ k, Carrier (sems.2 k).codec)
    (hrc : ∀ rc, rcOf rest = some rc → Carrier rc) :
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
      cases fs with
      | opt c => exact absurd rfl (hno c)
      | req c =>
        exact Finset.mem_filter.mpr ⟨reqPresentB_spec hreq hm, by simpa using hkn⟩
    · intro k
      exact entry_ranP' hsems hrc (funImage_some hd k)





/-! #### §2's clauses for the object's payload pair

Each is proved once, from core children, and both `lawfulCore_objectCodec` and
`lawful_objectCodec` consume them. -/

section ObjectLaws
variable {sems : MapOf FieldSem} {rest : RestSem}

/-- (R): a written row is complete, so reading it back is the entrywise round trip. -/
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
    · exact hfilter.symm
    · intro k h₁ h₂
      have hk1 : k ∈ p.1.filter (keepB rest sems ·) := by rw [hfilter]; exact h₁
      simp only [dif_pos hk1]

/-- (C): what was read is writable again by (C) at each stored entry. -/
theorem object_canon (hf : ∀ k, LawfulCore (sems.2 k).codec)
    (hrc : ∀ c ∈ rcOf rest, LawfulCore c) :
    ∀ q p, objRead sems (rcOf rest) (keepB rest sems) q = some p →
      (objWrite sems (rcOf rest) p).isSome = true := by
  rintro q p h
  obtain ⟨hreq, d, hd, rfl⟩ := objRead_eq.mp h
  have hval : valPresentB sems (q.1.filter (keepB rest sems ·)) = true := by
    refine valPresentB_of fun k fs hm hno => ?_
    have hknk : keepB rest sems k = true := keepB_of_declared k (by rw [hm]; rfl)
    cases fs with
    | opt c => exact absurd rfl (hno c)
    | req c => exact Finset.mem_filter.mpr ⟨reqPresentB_spec hreq hm, by simpa using hknk⟩
  have hstep : ∀ k : {k // k ∈ q.1.filter (keepB rest sems ·)},
      ((entryCodec sems (rcOf rest) k.1).bind (fun c => c.e (d k))).isSome = true := by
    intro k
    have hp := funImage_some hd k
    cases hc : entryCodec sems (rcOf rest) k.1 with
    | none => rw [hc] at hp; exact nomatch hp
    | some c =>
      simp only [hc, Option.bind_some] at hp ⊢
      exact (entryCodec_of hf hrc hc).canon hp
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
  have hp := funImage_some hd ⟨k, hx⟩
  have hw := funImage_some hg ⟨k, hx⟩
  cases hc : entryCodec sems (rcOf rest) k with
  | none => rw [hc] at hp; exact nomatch hp
  | some c =>
    simp only [hc, Option.bind_some] at hp hw
    exact (entryCodec_of hf hrc hc).agree hp hw

end ObjectLaws

/-- The keyed product — the doc's current-schema `object`. -/
theorem lawful_objectCodec {sems : MapOf FieldSem} {rest : RestSem}
    (hf : ∀ k, Lawful (sems.2 k).codec)
    (hrest : ∀ c, rest = .codec c → Lawful c) :
    Lawful (objectCodec sems rest) := by
  show Lawful (objectCodecCore sems (rcOf rest) (keepB rest sems))
  have hf' := fun k => (hf k).core
  have hrc' := fun c hc => ((rcOf_forall hrest) c hc).core
  exact objectCodecCore_eq ▸ lawful_carried (fun _ => rfl)
    (object_retract hf' hrc') (object_canon hf' hrc')
    (object_agree hf (rcOf_forall hrest))

theorem lawfulCore_objectCodec {sems : MapOf FieldSem} {rest : RestSem}
    (hf : ∀ k, LawfulCore (sems.2 k).codec)
    (hrest : ∀ c, rest = .codec c → LawfulCore c) :
    LawfulCore (objectCodec sems rest) := by
  show LawfulCore (objectCodecCore sems (rcOf rest) (keepB rest sems))
  exact objectCodecCore_eq ▸ lawfulCore_carried (fun _ => rfl)
    (object_retract hf (rcOf_forall hrest)) (object_canon hf (rcOf_forall hrest))

/-- **Compatibility**: `c` reads `a` as `t`. If `d` acts at `a` or at `t`, then `d` reads `a` as
    `t`. Pairwise, it is the classical compatibility of partial bijections, and it is the
    condition under which a union of lawful options is lawful. -/
def Compat (c d : Codec) : Prop :=
  ∀ a t, c.p a = some t → ((d.p a).isSome = true ∨ (d.e t).isSome = true) → d.p a = some t

/-- **Read agreement**: two compatible readings of one attribute give one value. -/
theorem Compat.p_agree {c d : Codec} (h : Compat c d) {a t w}
    (hc : c.p a = some t) (hd : d.p a = some w) : w = t := by
  have := h a t hc (Or.inl (by rw [hd]; rfl))
  rw [hd] at this; exact Option.some.inj this

/-- An attempted family has a first admitter wherever one of its options writes. -/
theorem find?_attempt_V {os : List OptionSem} (hatt : ∀ o ∈ os, o = .byAttempt o.c) {o v a}
    (ho : o ∈ os) (he : o.c.e v = some a) : ∃ o', os.find? (·.admitV v) = some o' :=
  Option.isSome_iff_exists.mp (List.find?_isSome.mpr
    ⟨o, ho, by rw [hatt o ho]; simp [OptionSem.byAttempt, he]⟩)

/-- …and wherever one of its options reads. -/
theorem find?_attempt_A {os : List OptionSem} (hatt : ∀ o ∈ os, o = .byAttempt o.c) {o a v}
    (ho : o ∈ os) (hp : o.c.p a = some v) : ∃ o', os.find? (·.admitA a) = some o' :=
  Option.isSome_iff_exists.mp (List.find?_isSome.mpr
    ⟨o, ho, by rw [hatt o ho]; simp [OptionSem.byAttempt, hp]⟩)

/-- The first admitter of an attempted family acts. -/
theorem acts_of_find?_V {os : List OptionSem} (hatt : ∀ o ∈ os, o = .byAttempt o.c) {o v}
    (hf : os.find? (·.admitV v) = some o) : (o.c.e v).isSome = true := by
  have hq := List.find?_some hf
  rw [hatt o (List.mem_of_find?_eq_some hf)] at hq; exact hq

/-- …and reads, on the attribute side. -/
theorem acts_of_find?_A {os : List OptionSem} (hatt : ∀ o ∈ os, o = .byAttempt o.c) {o a}
    (hf : os.find? (·.admitA a) = some o) : (o.c.p a).isSome = true := by
  have hq := List.find?_some hf
  rw [hatt o (List.mem_of_find?_eq_some hf)] at hq; exact hq

/-- Canonical reads: the codec writes each value that the codec reads at the attribute that
    the codec read. -/
def Canon (u : Codec) : Prop := ∀ a t, u.p a = some t → u.e t = some a

/-- **Write agreement**: two compatible options that both write `v` write one attribute. -/
theorem Compat.e_agree {c d : Codec} (h : Compat c d) (hc : LawfulCore c) (hd : Canon d) {v a b}
    (ha : c.e v = some a) (hb : d.e v = some b) : b = a := by
  have hp : d.p a = some v := h a v (hc.retract ha) (Or.inr (by rw [hb]; rfl))
  have := hd a v hp
  rw [hb] at this; exact Option.some.inj this

/-- **A union writes what any option writes**, over pairwise compatible, canonical options. -/
theorem altCodec_e_of_mem {os : List OptionSem} {μA : Option Member}
    (hatt : ∀ o ∈ os, o = .byAttempt o.c) (hl : ∀ o ∈ os, LawfulCore o.c)
    (hcan : ∀ o ∈ os, Canon o.c) (hC : ∀ o ∈ os, ∀ o' ∈ os, Compat o.c o'.c)
    {o v a} (ho : o ∈ os) (he : o.c.e v = some a) : (altCodec os μA).e v = some a := by
  obtain ⟨o', hf⟩ := find?_attempt_V hatt ho he
  have ho' := List.mem_of_find?_eq_some hf
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (acts_of_find?_V hatt hf)
  rw [(hC o ho o' ho').e_agree (hl o ho) (hcan o' ho') he hb] at hb
  exact altCodec_e.mpr ⟨o', hf, hb⟩

/-- **A union reads what any option reads**, over pairwise compatible options. -/
theorem altCodec_p_of_mem {os : List OptionSem} {μA : Option Member}
    (hatt : ∀ o ∈ os, o = .byAttempt o.c) (hC : ∀ o ∈ os, ∀ o' ∈ os, Compat o.c o'.c)
    {o a v} (ho : o ∈ os) (hp : o.c.p a = some v) : (altCodec os μA).p a = some v := by
  obtain ⟨o', hf⟩ := find?_attempt_A hatt ho hp
  have ho' := List.mem_of_find?_eq_some hf
  exact altCodec_p.mpr ⟨o', hf, hC o ho o' ho' _ _ hp (Or.inl (acts_of_find?_A hatt hf))⟩

/-- The sum's core laws. Compatibility is what makes them hold: the option that reads the
    attribute of a write reads the value back, whichever option wrote. -/
theorem lawfulCore_altCodec {os : List OptionSem} {μA : Option Member}
    (h : ∀ o ∈ os, LawfulCore o.c) (hatt : ∀ o ∈ os, o = .byAttempt o.c)
    (hC : ∀ o ∈ os, ∀ o' ∈ os, Compat o.c o'.c)
    (hW : ∀ m, μA = some m → ∀ o ∈ os, ∀ t a, o.c.e t = some a → a.member = m) :
    LawfulCore (altCodec os μA) where
  retract he := by
    obtain ⟨o, hf, hoe⟩ := altCodec_e.mp he
    have ho := List.mem_of_find?_eq_some hf
    have hop := (h o ho).retract hoe
    obtain ⟨o', hf'⟩ := find?_attempt_A hatt ho hop
    have ho' := List.mem_of_find?_eq_some hf'
    exact altCodec_p.mpr ⟨o', hf', hC o ho o' ho' _ _ hop (Or.inl (acts_of_find?_A hatt hf'))⟩
  canon hp := by
    obtain ⟨o, hf, hop⟩ := altCodec_p.mp hp
    have ho := List.mem_of_find?_eq_some hf
    obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp ((h o ho).canon hop)
    obtain ⟨o', hf'⟩ := find?_attempt_V hatt ho ha'
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (acts_of_find?_V hatt hf')
    exact Option.isSome_iff_exists.mpr ⟨b, altCodec_e.mpr ⟨o', hf', hb⟩⟩
  writes := by
    intro μ hμ t a he
    obtain ⟨o, hf, hoe⟩ := altCodec_e.mp he
    exact hW μ hμ o (List.mem_of_find?_eq_some hf) t a hoe

/-- …and (MP) with them: the option that read `a` as `t` also acts at `t`, so compatibility
    makes it read the attribute that the union writes, and `≼` holds at that option. -/
theorem lawful_altCodec {os : List OptionSem} {μA : Option Member}
    (h : ∀ o ∈ os, Lawful o.c) (hatt : ∀ o ∈ os, o = .byAttempt o.c)
    (hC : ∀ o ∈ os, ∀ o' ∈ os, Compat o.c o'.c)
    (hW : ∀ m, μA = some m → ∀ o ∈ os, ∀ t a, o.c.e t = some a → a.member = m) :
    Lawful (altCodec os μA) :=
  { lawfulCore_altCodec (fun o ho => (h o ho).core) hatt hC hW with
    agree := by
      intro a t a' hp he
      obtain ⟨o, hf, hop⟩ := altCodec_p.mp hp
      obtain ⟨o', hf', hoe⟩ := altCodec_e.mp he
      have ho := List.mem_of_find?_eq_some hf
      have ho' := List.mem_of_find?_eq_some hf'
      have hread : o'.c.p a = some t := hC o ho o' ho' _ _ hop (Or.inr (by rw [hoe]; rfl))
      exact (h o' ho').agree hread hoe }


/-! ### Kind separation, and `opaque`'s fixpoint

    The discharger `(opaque)` needs. An option is
    *pinned to a kind* when it admits only values and attributes of that kind — which is
    precisely what §3 means by calling `opaque`'s options "self-identifying". Pin each
    option and keep the kinds distinct, and compatibility follows with nothing said
    about what the options contain: `onKind_set` and its two neighbours hold for *any*
    element codec, which is why the fixpoint needs nothing from the recursive call. -/

/-- An option pinned to a kind: it admits only values and attributes of that kind. -/
def OptionSem.OnKind (o : OptionSem) (k : Kind) : Prop :=
  (∀ v, o.admitV v = true → v.kind = k) ∧ (∀ a, o.admitA a = true → a.kind = k)

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

/-- The number option is pinned to `number`. -/
theorem onKind_number : OptionSem.OnKind (.byAttempt numberCodec) .number := by
  constructor <;> intro x hx <;> cases x <;>
    simp_all [OptionSem.byAttempt, numberCodec, Value.kind, Attr.kind]

/-- A container option is pinned by its own constructor, whatever it contains. This is
    why the fixpoint's compatibility needs nothing from the recursive call — and why `opaque` is
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
theorem opaq_onKinds (fuel : Nat) :
    List.Forall₂ OptionSem.OnKind (opaqOptions (opaqCodec fuel)) opaqKinds :=
  .cons onKind_string (.cons onKind_boolean (.cons onKind_binary (.cons onKind_null
    (.cons onKind_number (.cons (onKind_set _) (.cons (onKind_array _)
      (.cons (onKind_record _) .nil)))))))

/-- Every option of `opaque` is lawful, given the recursive one is. -/
theorem lawful_opaqOptions {fuel : Nat} (hop : Lawful (opaqCodec fuel)) :
    ∀ o ∈ opaqOptions (opaqCodec fuel), Lawful o.c := by
  intro o ho
  simp only [opaqOptions, List.mem_cons] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
  exacts [lawful_stringCodec, lawful_booleanCodec, lawful_binaryCodec,
    lawful_nullCodec, lawful_numberCodec, lawful_setCodec hop, lawful_arrayCodec hop,
    lawful_recordCodec hop, absurd h (by simp)]

/-- **Exclusive admission gives compatibility.** Where the option that admits an input is the
    only one, the other option never acts where the first reads. -/
theorem compat_of_exclusive {os : List OptionSem} (hatt : ∀ o ∈ os, o = .byAttempt o.c)
    (hl : ∀ o ∈ os, LawfulCore o.c)
    (hxV : ∀ o ∈ os, ∀ v, o.admitV v = true → os.filter (·.admitV v) = [o])
    (hxA : ∀ o ∈ os, ∀ a, o.admitA a = true → os.filter (·.admitA a) = [o]) :
    ∀ o ∈ os, ∀ o' ∈ os, Compat o.c o'.c := by
  intro o ho o' ho' a t hp hact
  have hsame : o' = o := by
    rcases hact with hq | he
    · have hoA : o.admitA a = true := by rw [hatt o ho]; simp [OptionSem.byAttempt, hp]
      have ho'A : o'.admitA a = true := by rw [hatt o' ho']; exact hq
      have := (List.mem_filter (p := (·.admitA a))).mpr ⟨ho', ho'A⟩
      rw [hxA o ho a hoA] at this; exact List.mem_singleton.mp this
    · have hoV : o.admitV t = true := by rw [hatt o ho]; exact (hl o ho).canon hp
      have ho'V : o'.admitV t = true := by rw [hatt o' ho']; exact he
      have := (List.mem_filter (p := (·.admitV t))).mpr ⟨ho', ho'V⟩
      rw [hxV o ho t hoV] at this; exact List.mem_singleton.mp this
  subst hsame; exact hp

/-- `opaque`'s options are admitted by attempt. -/
theorem opaqOptions_attempt (rec : Codec) : ∀ o ∈ opaqOptions rec, o = .byAttempt o.c := by
  simp [opaqOptions, OptionSem.byAttempt]

/-- `opaque`'s options are pairwise compatible: each input has one kind, and one option
    answers to each kind. -/
theorem compat_opaque (fuel : Nat) (hop : Lawful (opaqCodec fuel)) :
    ∀ o ∈ opaqOptions (opaqCodec fuel), ∀ o' ∈ opaqOptions (opaqCodec fuel), Compat o.c o'.c := by
  have hz := opaq_onKinds fuel
  have hp : List.Pairwise (fun S T => ∀ l, S l → ¬ T l) (opaqKinds.map (fun k l => l = k)) := by
    rw [List.pairwise_map]
    exact (show opaqKinds.Nodup by decide).imp fun hne l hl hl' => hne (hl.symm.trans hl')
  refine compat_of_exclusive ?_ (fun o ho => (lawful_opaqOptions hop o ho).core) ?_ ?_
  · exact opaqOptions_attempt _
  · intro o ho v hv
    refine filter_eq_singleton_of_labels (key := fun v => some v.kind) ?_ hp o ho hv
    rw [List.forall₂_map_right_iff]
    exact hz.imp fun _ _ h v hv => ⟨_, rfl, h.1 v hv⟩
  · intro o ho a ha
    refine filter_eq_singleton_of_labels (key := fun a => some a.kind) ?_ hp o ho ha
    rw [List.forall₂_map_right_iff]
    exact hz.imp fun _ _ h a ha => ⟨_, rfl, h.2 a ha⟩

/-- `opaque` closes with no bespoke induction: the sum lemma, its options' lemmas, and
    compatibility computed from the shapes — kinds partition the values, and the same kinds
    partition the attributes. -/
theorem lawful_opaqCodec : ∀ (fuel : Nat), Lawful (opaqCodec fuel)
  | 0 => Lawful.empty
  | fuel+1 =>
    -- `μ` is `⊤`: the options name eight different members, so `unanimous` is `none`
    have hop : Lawful (opaqCodec fuel) := lawful_opaqCodec fuel
    lawful_altCodec (lawful_opaqOptions hop)
      (opaqOptions_attempt _) (compat_opaque fuel hop) (fun _ hm => nomatch hm)

end

end Calculus
