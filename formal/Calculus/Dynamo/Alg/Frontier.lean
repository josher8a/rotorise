import Calculus.Dynamo.Alg.Lawful

/-!
# Lawfulness — the open frontier

The laws that are stated and not yet discharged, and the ones whose discharge is partial.
`docs/roadmap.md` says which of these is a future state and what decides it.
-/

namespace Calculus

section
/-! ## Lawfulness — the open frontier (README roadmap) -/

/-! ### `setCodec`'s laws

On `Finset` these are the element codec's own laws, lifted by `setImage_inv`. The three set
payloads are three constructors, and non-emptiness is `Finset.Nonempty`, so no proof splits a
payload or carries a side condition. -/

/-- **(W) for `set`.** The wire member is `setMember` of the element's, and the kind that
    `setAt` takes is fixed by the element codec's own member. -/
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
    obtain ⟨k, S, rfl, hE⟩ := setCodec_f_eq.mp he
    obtain ⟨x₀, hx₀⟩ := S.2
    obtain ⟨a₀, ha₀⟩ := Option.isSome_iff_exists.mp (setAt_elem hE x₀ hx₀)
    have hm₀ : a₀.member = μ₀ := h.writes hc ha₀
    obtain ⟨k', hk'⟩ := setAt_some hE
    obtain ⟨T, hT, rfl⟩ := setAtK_eq.mp hk'
    have hs := setImage_some (neSetImage_eq_setImage.mp hT) x₀ hx₀
    rw [ha₀] at hs
    rw [← hm₀, Alg.Summand.member_of_out (s := k'.ground.summand) hs] at hμ
    exact Option.some.inj ((k'.wire_member T).symm.trans hμ)

/-- Writing a set succeeds when its elements do and the element member is ground: the member
    fixes the kind that `setAt` takes, and (R) supplies the injectivity. -/
theorem setAt_isSome_of {α : Type} {c : Codec} (h : LawfulCore c)
    {μ₀ μS : Member} (hsm : setMember μ₀ = some μS)
    {vinj : α → Value} (hvi : ∀ x y, vinj x = vinj y → x = y)
    {S : NEFinset α}
    (hall : ∀ x ∈ S.1, (c.e (vinj x)).isSome = true)
    (hmem : ∀ x ∈ S.1, ∀ a', c.e (vinj x) = some a' → a'.member = μ₀) :
    (setAt .host c vinj S).isSome = true := by
  obtain ⟨k, rfl⟩ := SetKind.of_setMember hsm
  obtain ⟨x₀, hx₀⟩ := S.2
  have hb : ∀ x ∈ S.1, ((c.e (vinj x)).bind k.elem.out).isSome = true := by
    intro x hx
    obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (hall x hx)
    obtain ⟨y, hy⟩ := SetKind.out_of_member (hmem x hx a' ha')
    rw [ha']
    exact Option.isSome_iff_exists.mpr ⟨y, hy⟩
  have hinj : ∀ x₁ ∈ S.1, ∀ x₂ ∈ S.1, ∀ y,
      (c.e (vinj x₁)).bind k.elem.out = some y → (c.e (vinj x₂)).bind k.elem.out = some y →
      x₁ = x₂ := fun x₁ _ x₂ _ y h1 h2 =>
    hvi _ _ ((h.retract (k.elem.bind_out h1)).symm.trans (h.retract (k.elem.bind_out h2))
      |> Option.some.inj)
  obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp (setImage_isSome_of hb hinj)
  have hK : setAtK .host c vinj S k = some (k.wire ⟨T, setImage_nonempty hT S.2⟩) :=
    setAtK_eq.mpr ⟨_, (neSetImage_eq_setImage (T := ⟨T, setImage_nonempty hT S.2⟩)).mpr hT, rfl⟩
  refine Option.isSome_iff_exists.mpr ⟨_, setAt_of hK fun k' hk' => ?_⟩
  -- every other kind misses: the image of `x₀` is a datum of the kind `k`
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (hb x₀ hx₀)
  have hmiss : (c.e (vinj x₀)).bind k'.elem.out = none := by
    rw [k.elem.bind_out hy]; exact SetKind.elem_out_ne (Ne.symm hk') y
  unfold setAtK
  rw [neSetImage_none (setImage_none_of hx₀ hmiss)]
  rfl

/-- **The inverse law for `set`**, at each orientation. The image inverts by `setImage_inv`
    through the element's own inverse law, and the reverse move lands on the kind of the input,
    because every other kind misses. -/
theorem set_inv {c : Codec} (h : Lawful c) {o : Alg.Orient} :
    ∀ {x y}, (setCodec c).f o x = some y → (setCodec c).f o.op y = some x := by
  -- the round trip of one kind: through `q` going out, back through `p`
  have key : ∀ {α β : Type} [DecidableEq α] [DecidableEq β] (p : Ctor α Attr) (q : Ctor β Attr)
      {S : NEFinset α} {T : NEFinset β},
      neSetImage (fun x => (c.f o (p.into x)).bind q.out) S = some T →
      neSetImage (fun y => (c.f o.op (q.into y)).bind p.out) T = some S := by
    intro α β _ _ p q S T hI
    refine neSetImage_eq_setImage.mpr (setImage_inv (fun x y hxy => ?_)
      (neSetImage_eq_setImage.mp hI))
    rw [h.inv (q.bind_out hxy)]; exact p.out_into x
  -- another kind `r` misses on the way back, because the input was a `p` set
  have miss : ∀ {α β γ : Type} [DecidableEq β] [DecidableEq γ] (p : Ctor α Attr)
      (q : Ctor β Attr) (r : Ctor γ Attr), (∀ x, r.out (p.into x) = none) →
      ∀ {S : NEFinset α} {T : NEFinset β},
      neSetImage (fun x => (c.f o (p.into x)).bind q.out) S = some T →
      neSetImage (fun y => (c.f o.op (q.into y)).bind r.out) T = none := by
    intro α β γ _ _ p q r hr S T hI
    obtain ⟨y, hy⟩ := T.2
    obtain ⟨x, -, hxy⟩ := (mem_setImage (neSetImage_eq_setImage.mp hI) y).mp hy
    exact neSetImage_none (setImage_none_of hy (by rw [h.inv (q.bind_out hxy)]; exact hr x))
  intro x y he
  obtain ⟨k, S, rfl, hE⟩ := setCodec_f_eq.mp he
  obtain ⟨k', hk'⟩ := setAt_some hE
  obtain ⟨T, hT, rfl⟩ := setAtK_eq.mp hk'
  refine setCodec_f_eq.mpr ⟨k', T, rfl, setAt_of (k := k)
    (setAtK_eq.mpr ⟨S, key k.elem k'.elem hT, rfl⟩) fun r hr => ?_⟩
  unfold setAtK
  rw [miss k.elem k'.elem r.elem (SetKind.elem_out_ne (Ne.symm hr)) hT]
  rfl

/-- **`setCodec` is lawful.** The inverse law is `set_inv`, and the member law `set_writes`;
    neither needs the element codec's index. -/
theorem lawful_setCodec {c : Codec} (h : Lawful c) : Lawful (setCodec c) where
  inv := set_inv h
  writes := set_writes h.core


/-! ### The keyed product

The slots, the entry steps, the rest policy and the two clauses of the codec record read no carrier
constructor, so they are the generic layer's. The two laws below are the generic ones at the `M`
prism. -/

/-- The keyed product — the doc's current-schema `object`. -/
theorem lawful_objectCodec {sems : MapOf FieldSem} {rest : RestSem} (hnf : Alg.noFill sems = true)
    (hf : ∀ k, Lawful (sems.2 k).codec)
    (hrest : ∀ c, rest = .codec c → Lawful c) :
    Lawful (objectCodec sems rest) :=
  Alg.lawful_objectCodec hnf hf hrest

end

end Calculus
