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

/-- A payload projection pins the member. -/
theorem member_of_sC {a : Attr} (h : (sC.out a).isSome = true) : a.member = .S := by
  cases a <;> simp_all [sC, Attr.member]
theorem member_of_nC {a : Attr} (h : (nC.out a).isSome = true) : a.member = .N := by
  cases a <;> simp_all [nC, Attr.member]
theorem member_of_bC {a : Attr} (h : (bC.out a).isSome = true) : a.member = .B := by
  cases a <;> simp_all [bC, Attr.member]



/-- `setAt` moves a string set when the element images are strings. -/
theorem setAt_ssBranch {α : Type} {o : Alg.Orient} {c : Codec} {inj : α → Attr} {S : NEFinset α}
    {T : NEFinset String}
    (h1 : neSetImage (fun x => (c.f o (inj x)).bind sC.out) S = some T) :
    setAt o c inj S = some (.ss T) := by
  unfold setAt; rw [h1]

/-- …a number set when they are numbers, the string branch having failed. -/
theorem setAt_nsBranch {α : Type} {o : Alg.Orient} {c : Codec} {inj : α → Attr} {S : NEFinset α}
    {T : NEFinset WFNumeral}
    (h0 : neSetImage (fun x => (c.f o (inj x)).bind sC.out) S = none)
    (h1 : neSetImage (fun x => (c.f o (inj x)).bind nC.out) S = some T) :
    setAt o c inj S = some (.ns T) := by
  unfold setAt; rw [h0, h1]

/-- …and a binary set when both earlier ones have. -/
theorem setAt_bsBranch {α : Type} {o : Alg.Orient} {c : Codec} {inj : α → Attr} {S : NEFinset α}
    {T : NEFinset Bytes}
    (h0 : neSetImage (fun x => (c.f o (inj x)).bind sC.out) S = none)
    (h0' : neSetImage (fun x => (c.f o (inj x)).bind nC.out) S = none)
    (h1 : neSetImage (fun x => (c.f o (inj x)).bind bC.out) S = some T) :
    setAt o c inj S = some (.bs T) := by
  unfold setAt; rw [h0, h0', h1]; rfl

/-- **(W) for `set`.** The wire member is `setMember` of the element's, and which branch
    `setAt` took is fixed by the element codec's own member. -/
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
    rcases setCodec_f_eq.mp he with ⟨S, rfl, hE⟩ | ⟨S, rfl, hE⟩ | ⟨S, rfl, hE⟩ <;>
      · obtain ⟨x₀, hx₀⟩ := S.2
        obtain ⟨a₀, ha₀⟩ := Option.isSome_iff_exists.mp (setAt_elem hE x₀ hx₀)
        have hm₀ : a₀.member = μ₀ := h.writes hc ha₀
        unfold setAt at hE
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
    member fixes which branch `setAt` takes, and (R) supplies the injectivity. -/
theorem setAt_isSome_of {α : Type} {c : Codec} (h : LawfulCore c)
    {μ₀ μS : Member} (hsm : setMember μ₀ = some μS)
    {vinj : α → Value} (hvi : ∀ x y, vinj x = vinj y → x = y)
    {S : NEFinset α}
    (hall : ∀ x ∈ S.1, (c.e (vinj x)).isSome = true)
    (hmem : ∀ x ∈ S.1, ∀ a', c.e (vinj x) = some a' → a'.member = μ₀) :
    (setAt .host c vinj S).isSome = true := by
  obtain ⟨x₀, hx₀⟩ := S.2
  unfold setAt
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
      rw [sC.into_out ho₁] at he₁
      rw [sC.into_out ho₂] at he₂
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
      rw [nC.into_out ho₁] at he₁
      rw [nC.into_out ho₂] at he₂
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
      rw [bC.into_out ho₁] at he₁
      rw [bC.into_out ho₂] at he₂
      exact hvi _ _ ((h.retract he₁).symm.trans (h.retract he₂) |> Option.some.inj)
    obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp (setImage_isSome_of hb hinj)
    rw [neSetImage_none hfailS, neSetImage_none hfailN,
      (neSetImage_eq_setImage (T := ⟨T, setImage_nonempty hT S.2⟩)).mpr hT]; rfl
  all_goals exact nomatch hsm


/-- **The inverse law for `set`**, at each orientation. The image inverts by `setImage_inv`
    through the element's own inverse law, and the reverse move lands on the branch of the input's
    wire set, because each earlier branch misses. -/
theorem set_inv {c : Codec} (h : Lawful c) {o : Alg.Orient} :
    ∀ {x y}, (setCodec c).f o x = some y → (setCodec c).f o.op y = some x := by
  -- the round trip of one branch: through `q` going out, back through `p`
  have key : ∀ {α β : Type} [DecidableEq α] [DecidableEq β] (p : Ctor α Attr) (q : Ctor β Attr)
      {S : NEFinset α} {T : NEFinset β},
      neSetImage (fun x => (c.f o (p.into x)).bind q.out) S = some T →
      neSetImage (fun y => (c.f o.op (q.into y)).bind p.out) T = some S := by
    intro α β _ _ p q S T hI
    refine neSetImage_eq_setImage.mpr (setImage_inv (fun x y hxy => ?_)
      (neSetImage_eq_setImage.mp hI))
    obtain ⟨a, ha, hq⟩ := Option.bind_eq_some_iff.mp hxy
    rw [q.into_out hq] at ha
    rw [h.inv ha]; exact p.out_into x
  -- an earlier branch `r` misses on the way back, because the input was a `p` set
  have miss : ∀ {α β γ : Type} [DecidableEq β] [DecidableEq γ] (p : Ctor α Attr)
      (q : Ctor β Attr) (r : Ctor γ Attr), (∀ x, r.out (p.into x) = none) →
      ∀ {S : NEFinset α} {T : NEFinset β},
      neSetImage (fun x => (c.f o (p.into x)).bind q.out) S = some T →
      neSetImage (fun y => (c.f o.op (q.into y)).bind r.out) T = none := by
    intro α β γ _ _ p q r hr S T hI
    obtain ⟨y, hy⟩ := T.2
    obtain ⟨x, -, hxy⟩ := (mem_setImage (neSetImage_eq_setImage.mp hI) y).mp hy
    obtain ⟨a, ha, hq⟩ := Option.bind_eq_some_iff.mp hxy
    rw [q.into_out hq] at ha
    exact neSetImage_none (setImage_none_of hy (by rw [h.inv ha]; exact hr x))
  intro x y he
  rcases setCodec_f_eq.mp he with ⟨S, rfl, hE⟩ | ⟨S, rfl, hE⟩ | ⟨S, rfl, hE⟩ <;>
    (unfold setAt at hE
     split at hE
     · next T hT =>
       injection hE with hE; subst hE
       first
       | exact setAt_ssBranch (key sC sC hT)
       | exact setAt_nsBranch (miss nC sC sC (fun _ => rfl) hT) (key nC sC hT)
       | exact setAt_bsBranch (miss bC sC sC (fun _ => rfl) hT) (miss bC sC nC (fun _ => rfl) hT)
           (key bC sC hT)
     · split at hE
       · next T hT =>
         injection hE with hE; subst hE
         first
         | exact setAt_ssBranch (key sC nC hT)
         | exact setAt_nsBranch (miss nC nC sC (fun _ => rfl) hT) (key nC nC hT)
         | exact setAt_bsBranch (miss bC nC sC (fun _ => rfl) hT) (miss bC nC nC (fun _ => rfl) hT)
             (key bC nC hT)
       · next =>
         obtain ⟨T, hT, hA⟩ := Option.map_eq_some_iff.mp hE
         subst hA
         first
         | exact setAt_ssBranch (key sC bC hT)
         | exact setAt_nsBranch (miss nC bC sC (fun _ => rfl) hT) (key nC bC hT)
         | exact setAt_bsBranch (miss bC bC sC (fun _ => rfl) hT) (miss bC bC nC (fun _ => rfl) hT)
             (key bC bC hT))

/-- **`setCodec` is lawful.** The inverse law is `set_inv`, and the member law `set_writes`;
    neither needs the element codec's index. -/
theorem lawful_setCodec {c : Codec} (h : Lawful c) : Lawful (setCodec c) where
  inv := set_inv h
  writes := set_writes h.core


/-! ### The keyed product

The guards, the entry steps, the rest policy and the two clauses of §2 read no carrier
constructor, so they are the generic layer's. The aliases give them their names here, and the
two laws below are the generic ones at the `M` prism. -/

export Alg (valPresentB_of)

/-- The keyed product — the doc's current-schema `object`. -/
theorem lawful_objectCodec {sems : MapOf FieldSem} {rest : RestSem}
    (hf : ∀ k, Lawful (sems.2 k).codec)
    (hrest : ∀ c, rest = .codec c → Lawful c) :
    Lawful (objectCodec sems rest) :=
  Alg.lawful_objectCodec (fun _ => rfl) hf hrest

/-! ### Kind separation

    The discharger of a recursive union. An option is *pinned to a kind* when it admits only
    values and attributes of that kind, which is what §3 means by "self-identifying". Pin each
    option and keep the kinds distinct, and compatibility follows with nothing said about what
    the options contain: `onKind_set` and its two neighbours hold for *any* element codec, so
    the fixpoint needs nothing from the recursive call. -/

/-- An option pinned to a kind: it admits only values and attributes of that kind. -/
def Codec.OnKind (o : Codec) (k : Kind) : Prop :=
  (∀ v, (o.e v).isSome = true → v.kind = k) ∧ (∀ a, (o.p a).isSome = true → a.kind = k)

/-! ### `opaque`'s options, each pinned to its kind -/

/-- **A base is pinned to its kind.** -/
theorem onKind_base (k : GroundKind) : Codec.OnKind (baseCodec k) k.kind := by
  cases k <;> constructor <;> intro x hx <;> cases x <;>
    simp_all [pointCodec, GroundKind.prism, sC, nC, bC, boolA, nullA, Attr.kind, Attr.member, Member.kind, GroundKind.kind, Alg.Codec.e, Alg.Codec.p]

/-- A container option is pinned by its own constructor, whatever it contains. This is
    why the fixpoint's compatibility needs nothing from the recursive call — and why `opaque` is
    not a special construction. -/
theorem onKind_set (c : Codec) : Codec.OnKind ((setCodec c)) .set := by
  constructor <;> intro x hx <;> cases x <;>
    simp_all [setCodec, Alg.Codec.e, Alg.Codec.p, Attr.kind, Attr.member, Member.kind]

theorem onKind_array (c : Codec) :
    Codec.OnKind ((arrayCodec c)) .array := by
  constructor <;> intro x hx <;> cases x <;>
    simp_all [arrayCodec, Alg.listCodec, carriedCodec, lA, Alg.Codec.e, Alg.Codec.p, Attr.kind, Attr.member, Member.kind]

theorem onKind_record (c : Codec) :
    Codec.OnKind ((recordCodec c)) .map := by
  refine ⟨fun v hv => ?_, fun a ha => ?_⟩
  · cases v
    case m keys f => rfl
    all_goals exact nomatch hv
  · cases a
    case m keys g => rfl
    all_goals exact nomatch ha

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

end

end Calculus
