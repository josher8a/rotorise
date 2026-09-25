import Calculus.Prisms

/-!
# Products

The traversal toolkit and the products built on it. `carriedCodec`, a payload pair carried
between two prisms, is the shape underneath all of them: `entrywise` is it at a traversal,
hence `arrayCodec` and `recordCodec`, and `tupleCodec` is it at `align` plus a traversal,
where the one fact worth proving is that alignment depends on a row's *length* alone.
`setCodec` is argued on its own. `drop` is a *filter* and not a traversal mode, so nothing
here needs a second toolkit.
-/

namespace Calculus

noncomputable section
/-! ## Filter facts (the sum proofs consume these) -/


/-! ## Products -/

/-- **The set image.** Map a finite set through a partial function, refusing if an element
    fails *or if two elements collide*.

    Not `Finset.image`, for two reasons. It dedups, which is the wrong answer here — (R)
    needs the element map injective, and collapsing two elements makes `p (e v) = v`
    unsatisfiable — so a collision must be refused, not absorbed. And its API is classical:
    `Finset.mem_image` and `Multiset.mem_dedup` depend on `Classical.choice`, which §3's
    axiom base does not admit. A `Nodup`-guarded `Multiset.map` needs neither. -/
noncomputable def setImage {α β : Type} [DecidableEq β]
    (f : α → Option β) (S : Finset α) : Option (Finset β) :=
  if h : ∀ x ∈ S, (f x).isSome then
    if hn : (S.attach.val.map (fun x => (f x.1).get (h x.1 x.2))).Nodup then
      some ⟨_, hn⟩
    else none
  else none

/-- Every element of the source maps. -/
theorem setImage_some {α β : Type} [DecidableEq β] {f : α → Option β} {S : Finset α}
    {T : Finset β} (h : setImage f S = some T) : ∀ x ∈ S, (f x).isSome := by
  unfold setImage at h
  split at h
  · next hall => exact hall
  · exact nomatch h

/-- …and the image contains exactly the elements' images. -/
theorem mem_setImage {α β : Type} [DecidableEq β] {f : α → Option β} {S : Finset α}
    {T : Finset β} (h : setImage f S = some T) (y : β) :
    y ∈ T ↔ ∃ x ∈ S, f x = some y := by
  unfold setImage at h
  split at h
  · next hall =>
    split at h
    · next hn =>
      injection h with h
      subst h
      constructor
      · intro hy
        simp only [Finset.mem_mk, Multiset.mem_map] at hy
        obtain ⟨x, -, hxy⟩ := hy
        exact ⟨x.1, x.2, by rw [← hxy]; exact (Option.some_get (hall x.1 x.2)).symm⟩
      · rintro ⟨x, hx, hfx⟩
        simp only [Finset.mem_mk, Multiset.mem_map]
        refine ⟨⟨x, hx⟩, Multiset.mem_attach _ _, ?_⟩
        rw [Option.get_of_mem (hall x hx) hfx]
    · exact nomatch h
  · exact nomatch h

/-- A non-empty set has a non-empty image. -/
theorem setImage_nonempty {α β : Type} [DecidableEq β] {f : α → Option β} {S : Finset α}
    {T : Finset β} (h : setImage f S = some T) (hs : S.Nonempty) : T.Nonempty := by
  obtain ⟨x, hx⟩ := hs
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (setImage_some h x hx)
  exact ⟨y, (mem_setImage h y).mpr ⟨x, hx, hy⟩⟩

/-- **The set image at `℘⁺fin`.** The same map, with non-emptiness carried rather than
    re-derived: `setImage_nonempty` is spent once, here, instead of at every call site.
    Everything else known about `setImage` transports through `neSetImage_eq_setImage`. -/
noncomputable def neSetImage {α β : Type} [DecidableEq β]
    (f : α → Option β) (S : NEFinset α) : Option (NEFinset β) :=
  match h : setImage f S.1 with
  | some T => some ⟨T, setImage_nonempty h S.2⟩
  | none => none

theorem neSetImage_eq_setImage {α β : Type} [DecidableEq β] {f : α → Option β}
    {S : NEFinset α} {T : NEFinset β} :
    neSetImage f S = some T ↔ setImage f S.1 = some T.1 := by
  unfold neSetImage
  split
  · next T' hT' =>
      refine ⟨fun h => ?_, fun h => ?_⟩
      · cases h; exact hT'
      · rw [hT'] at h; injection h with h; exact congrArg some (Subtype.ext h)
  · next hT' =>
      exact Iff.intro (fun h => nomatch h) (fun h => by rw [hT'] at h; exact nomatch h)

/-- …and `none` transports too. -/
theorem neSetImage_none {α β : Type} [DecidableEq β] {f : α → Option β} {S : NEFinset α}
    (h : setImage f S.1 = none) : neSetImage f S = none := by
  unfold neSetImage; split
  · next T' hT' => rw [h] at hT'; exact nomatch hT'
  · rfl

/-- **The constructor for `setImage`.** Given that every element maps, that the map is
    injective on the set, and a candidate image with the right membership, the image *is*
    that candidate. The injectivity hypothesis is what (R) supplies, and what `Finset.image`
    would have thrown away by dedupping. -/
theorem setImage_eq {α β : Type} [DecidableEq β] {f : α → Option β} {S : Finset α}
    {U : Finset β}
    (hall : ∀ x ∈ S, (f x).isSome)
    (hinj : ∀ x₁ ∈ S, ∀ x₂ ∈ S, ∀ y, f x₁ = some y → f x₂ = some y → x₁ = x₂)
    (hmem : ∀ y, y ∈ U ↔ ∃ x ∈ S, f x = some y) :
    setImage f S = some U := by
  unfold setImage
  rw [dif_pos hall]
  have hnd : (S.attach.val.map (fun x => (f x.1).get (hall x.1 x.2))).Nodup := by
    refine Multiset.Nodup.map_on ?_ S.attach.nodup
    intro x hx y hy hxy
    have hfx : f x.1 = some ((f x.1).get (hall x.1 x.2)) := (Option.some_get _).symm
    have hfy : f y.1 = some ((f y.1).get (hall y.1 y.2)) := (Option.some_get _).symm
    rw [hxy] at hfx
    exact Subtype.ext (hinj x.1 x.2 y.1 y.2 _ hfx hfy)
  rw [dif_pos hnd]
  congr 1
  apply Finset.ext
  intro y
  simp only [Finset.mem_mk, Multiset.mem_map, hmem y]
  constructor
  · rintro ⟨x, -, hxy⟩
    exact ⟨x.1, x.2, by rw [← hxy]; exact (Option.some_get (hall x.1 x.2)).symm⟩
  · rintro ⟨x, hx, hfx⟩
    exact ⟨⟨x, hx⟩, Multiset.mem_attach _ _, by rw [Option.get_of_mem (hall x hx) hfx]⟩

/-- **Inversion.** If the element map has a left inverse on its image, the set image
    inverts too. This is (R) lifted from elements to sets, and it is where the collision
    guard earns its place: without injectivity the image would be smaller than the source
    and could not invert. -/
theorem setImage_inv {α β : Type} [DecidableEq α] [DecidableEq β]
    {f : α → Option β} {g : β → Option α} {S : Finset α} {T : Finset β}
    (hfg : ∀ x y, f x = some y → g y = some x)
    (h : setImage f S = some T) : setImage g T = some S := by
  refine setImage_eq ?_ ?_ ?_
  · intro y hy
    obtain ⟨x, hx, hfx⟩ := (mem_setImage h y).mp hy
    rw [hfg x y hfx]; rfl
  · intro y₁ hy₁ y₂ hy₂ x hg₁ hg₂
    obtain ⟨x₁, hx₁, hf₁⟩ := (mem_setImage h y₁).mp hy₁
    obtain ⟨x₂, hx₂, hf₂⟩ := (mem_setImage h y₂).mp hy₂
    rw [hfg x₁ y₁ hf₁] at hg₁
    rw [hfg x₂ y₂ hf₂] at hg₂
    cases Option.some.inj hg₁
    cases Option.some.inj hg₂
    exact Option.some.inj (hf₁.symm.trans hf₂)
  · intro x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (setImage_some h x hx)
      exact ⟨y, (mem_setImage h y).mpr ⟨x, hx, hy⟩, hfg x y hy⟩
    · rintro ⟨y, hy, hgy⟩
      obtain ⟨x', hx', hf'⟩ := (mem_setImage h y).mp hy
      rw [hfg x' y hf'] at hgy
      cases Option.some.inj hgy
      exact hx'

/-- The round trip a set needs, assembled from the element codec's. -/
theorem setImage_roundTrip {α β : Type} [DecidableEq α] [DecidableEq β]
    {c : Codec} (h : LawfulCore c) {vinj : α → Value} {aout : Attr → Option β}
    {ainj : β → Attr} {vout : Value → Option α}
    (hA : ∀ a b, aout a = some b → a = ainj b)
    (hV : ∀ x, vout (vinj x) = some x)
    {S : Finset α} {T : Finset β}
    (hI : setImage (fun x => (c.e (vinj x)).bind aout) S = some T) :
    setImage (fun y => (c.p (ainj y)).bind vout) T = some S := by
  refine setImage_inv (fun x y hxy => ?_) hI
  simp only [Option.bind_eq_some_iff] at hxy
  obtain ⟨a, hea, hoa⟩ := hxy
  rw [hA a y hoa] at hea
  rw [h.retract hea]
  simpa using hV x

/-- One failing element sinks the image. -/
theorem setImage_none_of {α β : Type} [DecidableEq β] {f : α → Option β} {S : Finset α}
    {x : α} (hx : x ∈ S) (hf : f x = none) : setImage f S = none := by
  unfold setImage
  rw [dif_neg]
  intro hall
  have := hall x hx
  rw [hf] at this
  exact absurd this (by simp)

/-- The image succeeds when every element maps and no two collide. -/
theorem setImage_isSome_of {α β : Type} [DecidableEq β] {f : α → Option β} {S : Finset α}
    (hall : ∀ x ∈ S, (f x).isSome)
    (hinj : ∀ x₁ ∈ S, ∀ x₂ ∈ S, ∀ y, f x₁ = some y → f x₂ = some y → x₁ = x₂) :
    (setImage f S).isSome = true := by
  unfold setImage
  rw [dif_pos hall]
  have hnd : (S.attach.val.map (fun x => (f x.1).get (hall x.1 x.2))).Nodup := by
    refine Multiset.Nodup.map_on ?_ S.attach.nodup
    intro x hx y hy hxy
    have hfx : f x.1 = some ((f x.1).get (hall x.1 x.2)) := (Option.some_get _).symm
    have hfy : f y.1 = some ((f y.1).get (hall y.1 y.2)) := (Option.some_get _).symm
    rw [hxy] at hfx
    exact Subtype.ext (hinj x.1 x.2 y.1 y.2 _ hfx hfy)
  rw [dif_pos hnd]
  rfl

/-- **The image only looks at the set.** Two element maps agreeing on `S` have the same
    image — needed because `Codec.restrict` changes `e` everywhere and the set only sees it
    at its own members. -/
theorem setImage_congr {α β : Type} [DecidableEq β] {f g : α → Option β} {S : Finset α}
    (h : ∀ x ∈ S, f x = g x) : setImage f S = setImage g S := by
  have hiff : (∀ x ∈ S, (f x).isSome) ↔ (∀ x ∈ S, (g x).isSome) :=
    ⟨fun hh x hx => (h x hx) ▸ hh x hx, fun hh x hx => (h x hx).symm ▸ hh x hx⟩
  unfold setImage
  split
  · next hf =>
    have hg := hiff.mp hf
    rw [dif_pos hg]
    have hmap : (S.attach.val.map (fun x => (f x.1).get (hf x.1 x.2)))
        = (S.attach.val.map (fun x => (g x.1).get (hg x.1 x.2))) := by
      refine Multiset.map_congr rfl (fun x _ => ?_)
      exact Option.some.inj (by rw [Option.some_get, Option.some_get, h x.1 x.2])
    simp only [hmap]
  · next hf =>
    rw [dif_neg (fun hg => hf (hiff.mpr hg))]

/-- …and the same at `℘⁺fin`. -/
theorem neSetImage_congr {α β : Type} [DecidableEq β] {f g : α → Option β} {S : NEFinset α}
    (h : ∀ x ∈ S.1, f x = g x) : neSetImage f S = neSetImage g S := by
  cases hs : setImage f S.1 with
  | none => rw [neSetImage_none hs, neSetImage_none ((setImage_congr h).symm.trans hs)]
  | some T =>
    have hT : setImage g S.1 = some T := (setImage_congr h).symm.trans hs
    rw [(neSetImage_eq_setImage (T := ⟨T, setImage_nonempty hs S.2⟩)).mpr hs,
      (neSetImage_eq_setImage (T := ⟨T, setImage_nonempty hs S.2⟩)).mpr hT]

/-- Reading a value's scalar payload, the mirror of `sC`/`nC`/`bC` on the value side. -/
def vStr : Value → Option String := fun v => match v with | .str s => some s | _ => none
def vNum : Value → Option WFNumeral := fun v => match v with | .num d => some d | _ => none
def vBin : Value → Option Bytes  := fun v => match v with | .bin b => some b | _ => none

/-- A `bind` through a value projection pins the value. -/
theorem bind_vStr {o : Option Value} {y : String} (h : o.bind vStr = some y) :
    o = some (.str y) := by
  cases o with
  | none => exact nomatch h
  | some w => cases w <;> simp_all [vStr]

theorem bind_vNum {o : Option Value} {y : WFNumeral} (h : o.bind vNum = some y) :
    o = some (.num y) := by
  cases o with
  | none => exact nomatch h
  | some w => cases w <;> simp_all [vNum]

theorem bind_vBin {o : Option Value} {y : Bytes} (h : o.bind vBin = some y) :
    o = some (.bin y) := by
  cases o with
  | none => exact nomatch h
  | some w => cases w <;> simp_all [vBin]

/-- The member a set stores, computed from its element's (§3 `(set)`). -/
def setMember : Member → Option Member
  | .S => some .SS
  | .N => some .NS
  | .B => some .BS
  | _ => none

/-- Encode a value-set's payloads into the wire set their member selects. -/
noncomputable def encSet {α : Type} (c : Codec) (inj : α → Value) (S : NEFinset α) :
    Option Attr :=
  match neSetImage (fun x => (c.e (inj x)).bind sC.out) S with
  | some T => some (.ss T)
  | none => match neSetImage (fun x => (c.e (inj x)).bind nC.out) S with
    | some T => some (.ns T)
    | none => (neSetImage (fun x => (c.e (inj x)).bind bC.out) S).map Attr.bs

/-- …and back: decode a wire set's payloads into the value set their kind selects. -/
noncomputable def decSet {α : Type} (c : Codec) (inj : α → Attr) (S : NEFinset α) :
    Option Value :=
  match neSetImage (fun x => (c.p (inj x)).bind vStr) S with
  | some T => some (.strSet T)
  | none => match neSetImage (fun x => (c.p (inj x)).bind vNum) S with
    | some T => some (.numSet T)
    | none => (neSetImage (fun x => (c.p (inj x)).bind vBin) S).map Value.binSet

/-! No emptiness guard here: §1 types the wire sets as `℘⁺fin`, which is a type, so there is
no empty set for a codec to refuse. -/

/-- Writing a set needs every element to write. -/
theorem encSet_elem {α : Type} {c : Codec} {inj : α → Value} {S : NEFinset α} {a : Attr}
    (h : encSet c inj S = some a) : ∀ x ∈ S.1, (c.e (inj x)).isSome = true := by
  unfold encSet at h
  split at h
  · next T hT =>
      exact fun x hx => Option.isSome_of_isSome_bind (setImage_some (neSetImage_eq_setImage.mp hT) x hx)
  · split at h
    · next T hT =>
        exact fun x hx => Option.isSome_of_isSome_bind (setImage_some (neSetImage_eq_setImage.mp hT) x hx)
    · next =>
      obtain ⟨T, hT, -⟩ := Option.map_eq_some_iff.mp h
      exact fun x hx => Option.isSome_of_isSome_bind (setImage_some (neSetImage_eq_setImage.mp hT) x hx)

/-- …and reading one needs every element to read. -/
theorem decSet_elem {α : Type} {c : Codec} {inj : α → Attr} {S : NEFinset α} {v : Value}
    (h : decSet c inj S = some v) : ∀ x ∈ S.1, (c.p (inj x)).isSome = true := by
  unfold decSet at h
  split at h
  · next T hT =>
      exact fun x hx => Option.isSome_of_isSome_bind (setImage_some (neSetImage_eq_setImage.mp hT) x hx)
  · split at h
    · next T hT =>
        exact fun x hx => Option.isSome_of_isSome_bind (setImage_some (neSetImage_eq_setImage.mp hT) x hx)
    · next =>
      obtain ⟨T, hT, -⟩ := Option.map_eq_some_iff.mp h
      exact fun x hx => Option.isSome_of_isSome_bind (setImage_some (neSetImage_eq_setImage.mp hT) x hx)

/-- Two codecs that agree on the write of each element write one set. -/
theorem encSet_congr {α : Type} {c d : Codec} {inj : α → Value} {S : NEFinset α}
    (h : ∀ x ∈ S.1, c.e (inj x) = d.e (inj x)) : encSet c inj S = encSet d inj S := by
  unfold encSet
  rw [neSetImage_congr (S := S) (g := fun x => (d.e (inj x)).bind sC.out)
      (fun x hx => by rw [h x hx]),
    neSetImage_congr (S := S) (g := fun x => (d.e (inj x)).bind nC.out)
      (fun x hx => by rw [h x hx]),
    neSetImage_congr (S := S) (g := fun x => (d.e (inj x)).bind bC.out)
      (fun x hx => by rw [h x hx])]

/-- …and two codecs that agree on the read of each element read one set. -/
theorem decSet_congr {α : Type} {c d : Codec} {inj : α → Attr} {S : NEFinset α}
    (h : ∀ x ∈ S.1, c.p (inj x) = d.p (inj x)) : decSet c inj S = decSet d inj S := by
  unfold decSet
  rw [neSetImage_congr (S := S) (g := fun x => (d.p (inj x)).bind vStr)
      (fun x hx => by rw [h x hx]),
    neSetImage_congr (S := S) (g := fun x => (d.p (inj x)).bind vNum)
      (fun x hx => by rw [h x hx]),
    neSetImage_congr (S := S) (g := fun x => (d.p (inj x)).bind vBin)
      (fun x hx => by rw [h x hx])]

/-- What a read produces: one of the three value sets, each element read from an element
    of the wire set. -/
theorem decSet_mem {α : Type} {c : Codec} {inj : α → Attr} {S : NEFinset α} {v : Value}
    (h : decSet c inj S = some v) :
    (∃ T : NEFinset String, v = .strSet T ∧
        ∀ y ∈ T.1, ∃ x ∈ S.1, c.p (inj x) = some (.str y))
  ∨ (∃ T : NEFinset WFNumeral, v = .numSet T ∧
        ∀ y ∈ T.1, ∃ x ∈ S.1, c.p (inj x) = some (.num y))
  ∨ (∃ T : NEFinset Bytes, v = .binSet T ∧
        ∀ y ∈ T.1, ∃ x ∈ S.1, c.p (inj x) = some (.bin y)) := by
  unfold decSet at h
  split at h
  · next T hT =>
    injection h with h
    refine Or.inl ⟨T, h.symm, fun y hy => ?_⟩
    obtain ⟨x, hx, hxy⟩ := (mem_setImage (neSetImage_eq_setImage.mp hT) y).mp hy
    exact ⟨x, hx, bind_vStr hxy⟩
  · split at h
    · next T hT =>
      injection h with h
      refine Or.inr (Or.inl ⟨T, h.symm, fun y hy => ?_⟩)
      obtain ⟨x, hx, hxy⟩ := (mem_setImage (neSetImage_eq_setImage.mp hT) y).mp hy
      exact ⟨x, hx, bind_vNum hxy⟩
    · next =>
      obtain ⟨T, hT, hv⟩ := Option.map_eq_some_iff.mp h
      refine Or.inr (Or.inr ⟨T, hv.symm, fun y hy => ?_⟩)
      obtain ⟨x, hx, hxy⟩ := (mem_setImage (neSetImage_eq_setImage.mp hT) y).mp hy
      exact ⟨x, hx, bind_vBin hxy⟩

/-- §3 `(set)`. Non-emptiness, uniqueness and homogeneity are all carried by the **types**:
    a `Finset` has no repeats and no order, `℘⁺fin` has no empty inhabitant, and the three
    constructors are the three element types the reference names. What is left for the
    codec is the element map — and that is the whole of `(set)` now. -/
noncomputable def setCodec (c : Codec) : Codec :=
  { T := fun v => match v with
      | .strSet S => ∀ s ∈ S.1, c.T (.str s)
      | .numSet S => ∀ d ∈ S.1, c.T (.num d)
      | .binSet S => ∀ b ∈ S.1, c.T (.bin b)
      | _ => False
    μ := c.μ.bind setMember
    e := fun v => match v with
      | .strSet S => encSet c Value.str S
      | .numSet S => encSet c Value.num S
      | .binSet S => encSet c Value.bin S
      | _ => none
    p := fun a => match a with
      | .ss S => decSet c Attr.s S
      | .ns S => decSet c Attr.n S
      | .bs S => decSet c Attr.b S
      | _ => none }

/-! ### A set write, element by element -/

/-- …and a read. -/
theorem decSet_isSome_false {α : Type} {c : Codec} {inj : α → Attr} {S : NEFinset α}
    {x : α} (hx : x ∈ S.1) (h : c.p (inj x) = none) : (decSet c inj S).isSome = false := by
  cases hd : decSet c inj S with
  | none => rfl
  | some v =>
    have := decSet_elem hd x hx
    rw [h] at this; exact absurd this (by simp)

/-- Elements reading to strings take `decSet`'s first branch. The mirror of
    `encSet_isSome_of` at the read side, and it takes injectivity as a hypothesis rather
    than deriving it from `LawfulCore`: the read side's injectivity is **not** free —
    `numberCodec.p` went through the host's decimal reader, which rounds. -/
theorem decSet_isSome_str {α : Type} {c : Codec} {inj : α → Attr} {S : NEFinset α}
    (hall : ∀ x ∈ S.1, ((c.p (inj x)).bind vStr).isSome = true)
    (hinj : ∀ x₁ ∈ S.1, ∀ x₂ ∈ S.1, ∀ y, (c.p (inj x₁)).bind vStr = some y →
      (c.p (inj x₂)).bind vStr = some y → x₁ = x₂) :
    (decSet c inj S).isSome = true := by
  obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp (setImage_isSome_of hall hinj)
  unfold decSet
  rw [(neSetImage_eq_setImage (T := ⟨T, setImage_nonempty hT S.2⟩)).mpr hT]
  rfl

/-- …elements reading to a numeral take the second, the string branch having failed. -/
theorem decSet_isSome_num {α : Type} {c : Codec} {inj : α → Attr} {S : NEFinset α}
    {x₀ : α} (hx₀ : x₀ ∈ S.1)
    (hs : (c.p (inj x₀)).bind vStr = none)
    (hall : ∀ x ∈ S.1, ((c.p (inj x)).bind vNum).isSome = true)
    (hinj : ∀ x₁ ∈ S.1, ∀ x₂ ∈ S.1, ∀ y, (c.p (inj x₁)).bind vNum = some y →
      (c.p (inj x₂)).bind vNum = some y → x₁ = x₂) :
    (decSet c inj S).isSome = true := by
  obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp (setImage_isSome_of hall hinj)
  unfold decSet
  rw [neSetImage_none (setImage_none_of hx₀ hs),
    (neSetImage_eq_setImage (T := ⟨T, setImage_nonempty hT S.2⟩)).mpr hT]
  rfl

/-- …and elements reading to bytes take the third, the two before it having failed. -/
theorem decSet_isSome_bin {α : Type} {c : Codec} {inj : α → Attr} {S : NEFinset α}
    {x₀ : α} (hx₀ : x₀ ∈ S.1)
    (hs : (c.p (inj x₀)).bind vStr = none) (hn : (c.p (inj x₀)).bind vNum = none)
    (hall : ∀ x ∈ S.1, ((c.p (inj x)).bind vBin).isSome = true)
    (hinj : ∀ x₁ ∈ S.1, ∀ x₂ ∈ S.1, ∀ y, (c.p (inj x₁)).bind vBin = some y →
      (c.p (inj x₂)).bind vBin = some y → x₁ = x₂) :
    (decSet c inj S).isSome = true := by
  obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp (setImage_isSome_of hall hinj)
  unfold decSet
  rw [neSetImage_none (setImage_none_of hx₀ hs), neSetImage_none (setImage_none_of hx₀ hn),
    (neSetImage_eq_setImage (T := ⟨T, setImage_nonempty hT S.2⟩)).mpr hT]
  rfl

/-! ### A codec carried between two prisms

The shape underneath every product in §3–§4. A pair works on *payloads* — lists of
entries, mostly — and two prisms say which value and which attribute constructor hold
them. Retract, canon and writes split cleanly along that seam: the prism halves are discharged once,
here, and each construction is left with only its payload pair's own round trip,
definedness and agreement.

`pointCodec` above is the degenerate case, where the payload passes through untouched.
The three below are the products: `entrywise` (a traversal, hence `array` and `record`),
`tuple` (`align`, then a traversal) and `object` (a guard, a filter, then a traversal).

`set` is the one product that is *not* an instance, and for a reason worth stating: its
attribute side is a choice among three wire sets, not one constructor. It is argued on
its own below. -/

/-- **A codec between two prisms.** `P` is the held set's condition on the payload;
    `E`/`D` are the payload pair. -/
def carriedCodec {γ δ : Type} (V : Ctor γ Value) (A : Ctor δ Attr) (μ₀ : Member)
    (P : γ → Prop) (E : γ → Option δ) (D : δ → Option γ) : Codec :=
  { T := fun v => ∃ x, v = V.into x ∧ P x
    μ := some μ₀
    e := fun v => ((V.out v).bind E).map A.into
    p := fun a => ((A.out a).bind D).map V.into }

section Carried
variable {γ δ : Type} {V : Ctor γ Value} {A : Ctor δ Attr} {μ₀ : Member}
  {P : γ → Prop} {E : γ → Option δ} {D : δ → Option γ}

/-- What it writes: only a value the prism matches, and only what `E` accepts. -/
theorem carried_e {v a} :
    (carriedCodec V A μ₀ P E D).e v = some a ↔
      ∃ x y, V.out v = some x ∧ E x = some y ∧ a = A.into y := by
  simp [carriedCodec, Option.bind_eq_some_iff, Option.map_eq_some_iff, eq_comm (a := a)]

/-- What it reads: the mirror. -/
theorem carried_p {a v} :
    (carriedCodec V A μ₀ P E D).p a = some v ↔
      ∃ y x, A.out a = some y ∧ D y = some x ∧ v = V.into x := by
  simp [carriedCodec, Option.bind_eq_some_iff, Option.map_eq_some_iff, eq_comm (a := v)]

/-- (R), (C) and (W) are the payload pair's own, plus the member the attribute
    constructor stamps. The prisms contribute nothing but their two laws. -/
theorem lawfulCore_carried (hμ : ∀ y, (A.into y).member = μ₀)
    (hr : ∀ x y, E x = some y → D y = some x)
    (hc : ∀ y x, D y = some x → (E x).isSome) :
    LawfulCore (carriedCodec V A μ₀ P E D) where
  retract he := by
    obtain ⟨x, y, hv, hx, rfl⟩ := carried_e.mp he
    exact carried_p.mpr ⟨y, x, A.out_into y, hr x y hx, V.into_out hv⟩
  canon hp := by
    obtain ⟨y, x, _, hy, rfl⟩ := carried_p.mp hp
    obtain ⟨y', h'⟩ := Option.isSome_iff_exists.mp (hc y x hy)
    exact Option.isSome_iff_exists.mpr ⟨_, carried_e.mpr ⟨x, y', V.out_into x, h', rfl⟩⟩
  writes := by
    intro μ hμ' t a he
    obtain ⟨_, y, _, _, rfl⟩ := carried_e.mp he
    exact (hμ y).trans (Option.some.inj hμ')

/-- Canonical reads are the payload pair's own too. -/
theorem lawful_carried (hμ : ∀ y, (A.into y).member = μ₀)
    (hr : ∀ x y, E x = some y → D y = some x)
    (hcan : ∀ y x, D y = some x → E x = some y) :
    Lawful (carriedCodec V A μ₀ P E D) :=
  have hc := lawfulCore_carried (P := P) hμ hr (fun y x h => by rw [hcan y x h]; rfl)
  { retract := hc.retract
    writes := hc.writes
    canon := by
      intro a t hp
      obtain ⟨y, x, ha, hy, rfl⟩ := carried_p.mp hp
      exact carried_e.mpr ⟨x, y, V.out_into x, hcan y x hy, A.into_out ha⟩ }

/-- `e : T ⇀ 𝔸` and `p : 𝔸 ⇀ T`: the held set's condition has to hold of whatever
    payload either half of the pair accepts. -/
theorem carrier_carried
    (hdom : ∀ {x y}, E x = some y → P x)
    (hran : ∀ {y x}, D y = some x → P x) :
    Carrier (carriedCodec V A μ₀ P E D) where
  domE he := by
    obtain ⟨x, y, hv, hx, _⟩ := carried_e.mp he
    exact ⟨x, V.into_out hv, hdom hx⟩
  ranP hp := by
    obtain ⟨y, x, _, hy, rfl⟩ := carried_p.mp hp
    exact ⟨x, rfl, hran hy⟩

end Carried

/-! ### The entrywise product, named once

`array` and `record` are `carriedCodec` where the payload pair is one entry function
traversed: a value constructor holding a list of entries, an attribute constructor
holding a list of wire entries. Named once, §2's laws are discharged once. -/

/-- **The entrywise product**: `carriedCodec` at a traversal. -/
def entrywise {α β : Type} (V : Ctor (List α) Value) (A : Ctor (List β) Attr)
    (μ₀ : Member) (P : List α → Prop) (f : α → Option β) (g : β → Option α) : Codec :=
  carriedCodec V A μ₀ P (traverse f) (traverse g)

section Entrywise
variable {α β : Type} {V : Ctor (List α) Value} {A : Ctor (List β) Attr}
  {μ₀ : Member} {P : List α → Prop} {f : α → Option β} {g : β → Option α}

/-- Canonical reads, entry by entry. -/
theorem lawful_entrywise (hμ : ∀ ys, (A.into ys).member = μ₀)
    (hr : ∀ x y, f x = some y → g y = some x)
    (hcan : ∀ y x, g y = some x → f x = some y) :
    Lawful (entrywise V A μ₀ P f g) :=
  lawful_carried hμ (traverse_roundTrip hr) (traverse_roundTrip hcan)

theorem carrier_entrywise
    (hdom : ∀ {xs ys}, traverse f xs = some ys → P xs)
    (hran : ∀ {ys xs}, traverse g ys = some xs → P xs) :
    Carrier (entrywise V A μ₀ P f g) :=
  carrier_carried hdom hran

end Entrywise

/-! ### `array` (§3) — entrywise between `arr` and `L` -/

/-! ### What `set` writes and reads

    The attribute side of `set` is a choice among three wire constructors rather than
    one prism, which is why it is not an `entrywise` product and why its read-side
    inversion names all three families. -/

/-- What `set` writes: one of the three value-set constructors, its payloads imaged
    through the element codec. -/
theorem setCodec_e_eq {c : Codec} {v : Value} {a : Attr} :
    (setCodec c).e v = some a ↔
      (∃ S : NEFinset String, v = .strSet S ∧ encSet c Value.str S = some a)
      ∨ (∃ S : NEFinset WFNumeral, v = .numSet S ∧ encSet c Value.num S = some a)
      ∨ (∃ S : NEFinset Bytes, v = .binSet S ∧ encSet c Value.bin S = some a) := by
  cases v <;> simp [setCodec]

/-- …and what it reads: one of the three wire sets, imaged back. -/
theorem setCodec_p_eq {c : Codec} {a : Attr} {v : Value} :
    (setCodec c).p a = some v ↔
      (∃ S : NEFinset String, a = .ss S ∧ decSet c Attr.s S = some v)
      ∨ (∃ S : NEFinset WFNumeral, a = .ns S ∧ decSet c Attr.n S = some v)
      ∨ (∃ S : NEFinset Bytes, a = .bs S ∧ decSet c Attr.b S = some v) := by
  cases a <;> simp [setCodec]

def arrayCodec (c : Codec) : Codec :=
  { T := fun v => match v with | .arr vs => ∀ x ∈ vs, c.T x | _ => False
    μ := some .L
    e := fun v => match v with
      | .arr vs => (traverse c.e vs).map Attr.l
      | _ => none
    p := fun a => match a with
      | .l as => (traverse c.p as).map Value.arr
      | _ => none }

/-- `array` *is* the entrywise product at `arr`/`L`, on the nose. The definition above is
    left in its unfolded form because the `opaque` fixpoint reduces through it; this
    equation is what carries the three lemmas across. -/
theorem arrayCodec_eq {c : Codec} :
    arrayCodec c = entrywise arrV lA .L (fun vs => ∀ x ∈ vs, c.T x) c.e c.p := by
  ext v <;> cases v <;> simp_all [arrayCodec, entrywise, carriedCodec, arrV, lA]

/-- `array` is lawful, entry by entry. -/
theorem lawful_arrayCodec {c : Codec} (h : Lawful c) : Lawful (arrayCodec c) :=
  arrayCodec_eq ▸ lawful_entrywise (fun _ => rfl) (fun _ _ => h.retract) (fun _ _ => h.canon)

theorem carrier_arrayCodec {c : Codec} (hc : Carrier c) : Carrier (arrayCodec c) :=
  arrayCodec_eq ▸ carrier_entrywise
    (fun h => traverse_mem_input (fun _ _ => hc.domE) h)
    (fun h => traverse_mem (fun _ _ => hc.ranP) h)

/-! ### `record` (§3) — `carriedCodec` between `map` and `M`

The keyed entry steps ~~encPair~~/~~decPair~~ are gone with the traversal. They existed to
carry a name past a codec inside `traverse`, and `M`'s payload no longer has a list for
`traverse` to walk: the names are the index, so `funImage` moves the entry function and
nothing has to carry a name anywhere. Their five laws went with them — §2's four, one
level down, were what `entrywise` asked and `carriedCodec` does not. -/

noncomputable def recordCodec (c : Codec) : Codec :=
  { T := fun v => match v with | .map _ f => ∀ k, c.T (f k) | _ => False
    μ := some .M
    e := fun v => match v with
      | .map keys f => (funImage (fun k => c.e (f k))).map (Attr.m keys)
      | _ => none
    p := fun a => match a with
      | .m keys g => (funImage (fun k => c.p (g k))).map (Value.map keys)
      | _ => none }

/-! `record` is no longer an `entrywise` product: `entrywise` traverses a *list* payload,
and `M`'s payload is a name set with a function on it. What it still is, is `carriedCodec`
between the same two prisms — `carriedCodec` is generic in the payload — so the shape of
the derivation survives even though the traversal does not. These three are direct, and
short, because `funImage` does the work `traverse` used to. -/

/-- What `record` writes and reads: the same name set, every value through `c`. -/
theorem recordCodec_e_eq {c : Codec} {v : Value} {a : Attr} :
    (recordCodec c).e v = some a ↔
      ∃ keys f g, v = .map keys f ∧ funImage (fun k => c.e (f k)) = some g ∧
        a = .m keys g := by
  cases v
  case map keys f =>
    constructor
    · intro h
      obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp h
      exact ⟨keys, f, g, rfl, hg, rfl⟩
    · rintro ⟨keys', f', g, hv, hg, rfl⟩
      cases hv
      show (funImage (fun k => c.e (f k))).map (Attr.m keys) = _
      rw [hg]; rfl
  all_goals
    constructor
    · intro h
      exact nomatch h
    · rintro ⟨_, _, _, hv, -, -⟩
      exact nomatch hv

theorem recordCodec_p_eq {c : Codec} {a : Attr} {v : Value} :
    (recordCodec c).p a = some v ↔
      ∃ keys g f, a = .m keys g ∧ funImage (fun k => c.p (g k)) = some f ∧
        v = .map keys f := by
  cases a
  case m keys g =>
    constructor
    · intro h
      obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp h
      exact ⟨keys, g, f, rfl, hf, rfl⟩
    · rintro ⟨keys', g', f, ha, hf, rfl⟩
      cases ha
      show (funImage (fun k => c.p (g k))).map (Value.map keys) = _
      rw [hf]; rfl
  all_goals
    constructor
    · intro h
      exact nomatch h
    · rintro ⟨_, _, _, ha, -, -⟩
      exact nomatch ha

/-- (R), (C), (W) — `M` is the member every `map` writes. -/
theorem lawfulCore_recordCodec {c : Codec} (h : LawfulCore c) :
    LawfulCore (recordCodec c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t a he
    obtain ⟨keys, f, g, rfl, hg, rfl⟩ := recordCodec_e_eq.mp he
    exact recordCodec_p_eq.mpr ⟨keys, g, f, rfl,
      funImage_eq (fun k => h.retract (funImage_some hg k)), rfl⟩
  · intro a t hp
    obtain ⟨keys, g, f, rfl, hf, rfl⟩ := recordCodec_p_eq.mp hp
    have := funImage_isSome (keys := keys) (g := fun k => c.e (f k))
      (fun k => h.canon (funImage_some hf k))
    simpa [recordCodec] using this
  · intro μ hμ t a he
    obtain ⟨keys, f, g, rfl, -, rfl⟩ := recordCodec_e_eq.mp he
    simpa [Attr.member] using Option.some.inj hμ

/-- `record` is lawful, name by name. -/
theorem lawful_recordCodec {c : Codec} (h : Lawful c) : Lawful (recordCodec c) := by
  refine ⟨(lawfulCore_recordCodec h.core).retract, ?_, (lawfulCore_recordCodec h.core).writes⟩
  intro a t hp
  obtain ⟨keys, g, f, rfl, hf, rfl⟩ := recordCodec_p_eq.mp hp
  exact recordCodec_e_eq.mpr ⟨keys, f, g, rfl,
    funImage_eq (fun k => h.canon (funImage_some hf k)), rfl⟩

theorem carrier_recordCodec {c : Codec} (hc : Carrier c) : Carrier (recordCodec c) where
  domE {v a} he := by
    obtain ⟨keys, f, g, rfl, hg, rfl⟩ := recordCodec_e_eq.mp he
    exact fun k => hc.domE (funImage_some hg k)
  ranP {a v} hp := by
    obtain ⟨keys, g, f, rfl, hf, rfl⟩ := recordCodec_p_eq.mp hp
    exact fun k => hc.ranP (funImage_some hf k)

/-! ### `tuple` (§3) — the positional product

`tuple` is `carriedCodec` between the same two prisms as `array`, with a payload pair
that pairs each position with its own codec before traversing. Everything specific to it
is therefore a fact about that pairing, and there is only one worth stating: **which
codec a position gets depends on the position alone, never on what stands there.** Name
the codec row a shape assigns to a row of `n` positions (`slots`) and the pairing is a
`zip` with it (`align_eq_some`) — after which a row and its image under the pair, having
the same length, provably align against the *same* codecs. That is the whole of the
tuple's asymmetry between reading and writing, and the four clauses of §2 then run
position by position over the codec row, exactly as they do for `array`. -/

/-- Pair each position with its codec: the fixed head positionally, the tail
    uniformly; length mismatches refuse. `tuple` is then `align` + `traverse`. -/
def align {α : Type} : List Codec → Option Codec → List α → Option (List (Codec × α))
  | [], _, [] => some []
  | [], tail, x :: xs =>
    match tail with
    | some c => (align [] tail xs).map ((c, x) :: ·)
    | none => none
  | _ :: _, _, [] => none
  | c :: cs, tail, x :: xs => (align cs tail xs).map ((c, x) :: ·)

def tupleCodec (cs : List Codec) (tail : Option Codec) : Codec :=
  { T := fun v => match v with
      | .arr vs => ∃ ps, align cs tail vs = some ps ∧ ∀ p ∈ ps, p.1.T p.2
      | _ => False
    μ := some .L
    e := fun v => match v with
      | .arr vs => ((align cs tail vs).bind
          (traverse fun cv => cv.1.e cv.2)).map Attr.l
      | _ => none
    p := fun a => match a with
      | .l as => ((align cs tail as).bind
          (traverse fun ca => ca.1.p ca.2)).map Value.arr
      | _ => none }

/-! #### The codec row a shape assigns -/

/-- The codec row for a row of `n` positions: the fixed head, then the tail codec as
    often as needed. `none` is the length mismatch `align` refuses on. -/
def slots : List Codec → Option Codec → Nat → Option (List Codec)
  | [], _, 0 => some []
  | [], none, _ + 1 => none
  | [], some c, n + 1 => (slots [] (some c) n).map (c :: ·)
  | _ :: _, _, 0 => none
  | c :: cs, tail, n + 1 => (slots cs tail n).map (c :: ·)

theorem align_eq_zip {α : Type} : ∀ (cs : List Codec) (tail : Option Codec) (xs : List α),
    align cs tail xs = (slots cs tail xs.length).map (·.zip xs)
  | [], tail, [] => by cases tail <;> rfl
  | [], none, _ :: _ => rfl
  | [], some c, x :: xs => by
      show (align [] (some c) xs).map ((c, x) :: ·) = _
      rw [align_eq_zip [] (some c) xs]
      cases hs : slots [] (some c) xs.length <;> simp [slots, hs, List.zip]
  | _ :: _, tail, [] => by cases tail <;> rfl
  | c :: cs, tail, x :: xs => by
      show (align cs tail xs).map ((c, x) :: ·) = _
      rw [align_eq_zip cs tail xs]
      cases hs : slots cs tail xs.length <;> simp [slots, hs, List.zip]

theorem slots_length : ∀ (cs : List Codec) (tail : Option Codec) (n : Nat) (ds),
    slots cs tail n = some ds → ds.length = n
  | [], tail, 0, _, h => by cases tail <;> (simp [slots] at h; simp [← h])
  | [], some c, n + 1, ds, h => by
      obtain ⟨ds', h', rfl⟩ := Option.map_eq_some_iff.mp h
      simp [slots_length [] (some c) n ds' h']
  | c :: cs, tail, n + 1, ds, h => by
      obtain ⟨ds', h', rfl⟩ := Option.map_eq_some_iff.mp h
      simp [slots_length cs tail n ds' h']

/-- Every codec in the row is one the shape declared. -/
theorem slots_mem : ∀ (cs : List Codec) (tail : Option Codec) (n : Nat) (ds),
    slots cs tail n = some ds → ∀ c ∈ ds, c ∈ cs ∨ tail = some c
  | [], tail, 0, _, h, _, hm => by
      cases tail <;> (simp [slots] at h; subst h; exact nomatch hm)
  | [], some c, n + 1, ds, h, d, hm => by
      obtain ⟨ds', h', rfl⟩ := Option.map_eq_some_iff.mp h
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact .inr rfl
      · exact slots_mem [] (some c) n ds' h' d hm'
  | c :: cs, tail, n + 1, ds, h, d, hm => by
      obtain ⟨ds', h', rfl⟩ := Option.map_eq_some_iff.mp h
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact .inl (List.mem_cons_self)
      · exact (slots_mem cs tail n ds' h' d hm').imp (List.mem_cons_of_mem _) id

/-- A property of the shape's codecs is a property of every codec in every row. -/
theorem slots_all {Q : Codec → Prop} {cs : List Codec} {tail : Option Codec}
    (hcs : ∀ c ∈ cs, Q c) (htl : ∀ c ∈ tail, Q c) {n ds}
    (hs : slots cs tail n = some ds) : ∀ c ∈ ds, Q c := fun c hc =>
  (slots_mem cs tail n ds hs c hc).elim (hcs c) (htl c)

/-- **The pivot for `align`.** An alignment is the codec row zipped with the row: which
    codec a position gets depends on the position alone, never on what stands there. -/
theorem align_eq_some {α : Type} {cs : List Codec} {tail : Option Codec}
    {xs : List α} {ps} :
    align cs tail xs = some ps ↔
      ∃ ds, slots cs tail xs.length = some ds ∧ ds.length = xs.length ∧ ps = ds.zip xs := by
  rw [align_eq_zip]
  constructor
  · intro h
    obtain ⟨ds, h', rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨ds, h', slots_length _ _ _ _ h', rfl⟩
  · rintro ⟨ds, h', _, rfl⟩
    rw [h']; rfl

/-- …so any row of the same length aligns against the same codecs. -/
theorem align_of_slots {α : Type} {cs : List Codec} {tail : Option Codec} {n ds}
    (h : slots cs tail n = some ds) {xs : List α} (hn : xs.length = n) :
    align cs tail xs = some (ds.zip xs) := by
  rw [align_eq_zip, hn, h]; rfl

/-! #### §2's clauses, position by position over the codec row -/

theorem zip_roundTrip : ∀ (ds : List Codec) (vs : List Value) (as : List Attr),
    (∀ c ∈ ds, LawfulCore c) → ds.length = vs.length →
    traverse (fun cv : Codec × Value => cv.1.e cv.2) (ds.zip vs) = some as →
    traverse (fun ca : Codec × Attr => ca.1.p ca.2) (ds.zip as) = some vs
  | [], vs, as, _, hlen, h => by simp_all [List.eq_nil_of_length_eq_zero hlen.symm]
  | _ :: _, [], as, _, hlen, h => by simp_all
  | d :: ds, v :: vs, as, hd, hlen, h => by
      rw [List.zip_cons_cons, traverse_cons] at h
      obtain ⟨a, ha, has⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨as', has', rfl⟩ := Option.map_eq_some_iff.mp has
      rw [List.zip_cons_cons, traverse_cons, (hd d (by simp)).retract ha,
        zip_roundTrip ds vs as' (fun c hc => hd c (by simp [hc])) (by simpa using hlen) has']
      rfl

theorem zip_canon : ∀ (ds : List Codec) (as : List Attr) (vs : List Value),
    (∀ c ∈ ds, LawfulCore c) →
    traverse (fun ca : Codec × Attr => ca.1.p ca.2) (ds.zip as) = some vs →
    (traverse (fun cv : Codec × Value => cv.1.e cv.2) (ds.zip vs)).isSome
  | [], as, vs, _, h => by simp_all
  | _ :: _, [], vs, _, h => by simp_all
  | d :: ds, a :: as, vs, hd, h => by
      rw [List.zip_cons_cons, traverse_cons] at h
      obtain ⟨v, hv, hvs⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨vs', hvs', rfl⟩ := Option.map_eq_some_iff.mp hvs
      obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp ((hd d (by simp)).canon hv)
      obtain ⟨as', has'⟩ := Option.isSome_iff_exists.mp
        (zip_canon ds as vs' (fun c hc => hd c (by simp [hc])) hvs')
      simp [List.zip_cons_cons, traverse_cons, ha', has']

/-- Reading a row and writing it back gives the row: canonical reads, position by position. -/
theorem zip_canonS : ∀ (ds : List Codec) (as : List Attr) (vs : List Value),
    (∀ c ∈ ds, Lawful c) → ds.length = as.length →
    traverse (fun ca : Codec × Attr => ca.1.p ca.2) (ds.zip as) = some vs →
    traverse (fun cv : Codec × Value => cv.1.e cv.2) (ds.zip vs) = some as
  | [], as, vs, _, hlen, h => by simp_all [List.eq_nil_of_length_eq_zero hlen.symm]
  | _ :: _, [], vs, _, hlen, h => by simp_all
  | d :: ds, a :: as, vs, hd, hlen, h => by
      rw [List.zip_cons_cons, traverse_cons] at h
      obtain ⟨v, hv, hvs⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨vs', hvs', rfl⟩ := Option.map_eq_some_iff.mp hvs
      rw [List.zip_cons_cons, traverse_cons, (hd d (by simp)).canon hv,
        zip_canonS ds as vs' (fun c hc => hd c (by simp [hc])) (by simpa using hlen) hvs']
      rfl

/-- Writing a row puts every position on its own carrier… -/
theorem zip_domE : ∀ (ds : List Codec) (vs : List Value) (as : List Attr),
    (∀ c ∈ ds, Carrier c) →
    traverse (fun cv : Codec × Value => cv.1.e cv.2) (ds.zip vs) = some as →
    ∀ q ∈ ds.zip vs, q.1.T q.2
  | [], vs, as, _, h => by simp_all
  | _ :: _, [], as, _, h => by simp_all
  | d :: ds, v :: vs, as, hd, h => by
      rw [List.zip_cons_cons, traverse_cons] at h
      obtain ⟨a, ha, has⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨as', has', rfl⟩ := Option.map_eq_some_iff.mp has
      intro q hq
      rcases List.mem_cons.mp (by simpa using hq) with rfl | hq'
      · exact (hd d (by simp)).domE ha
      · exact zip_domE ds vs as' (fun c hc => hd c (by simp [hc])) has' q hq'

/-- …and so does reading one. -/
theorem zip_ranP : ∀ (ds : List Codec) (as : List Attr) (vs : List Value),
    (∀ c ∈ ds, Carrier c) →
    traverse (fun ca : Codec × Attr => ca.1.p ca.2) (ds.zip as) = some vs →
    ∀ q ∈ ds.zip vs, q.1.T q.2
  | [], as, vs, _, h => by simp_all
  | _ :: _, [], vs, _, h => by simp_all
  | d :: ds, a :: as, vs, hd, h => by
      rw [List.zip_cons_cons, traverse_cons] at h
      obtain ⟨v, hv, hvs⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨vs', hvs', rfl⟩ := Option.map_eq_some_iff.mp hvs
      intro q hq
      rcases List.mem_cons.mp (by simpa using hq) with rfl | hq'
      · exact (hd d (by simp)).ranP hv
      · exact zip_ranP ds as vs' (fun c hc => hd c (by simp [hc])) hvs' q hq'

/-! #### `tuple` is `carriedCodec` at that pair -/

section Tuple
variable {cs : List Codec} {tail : Option Codec}

theorem tupleCodec_eq :
    tupleCodec cs tail = carriedCodec arrV lA .L
      (fun vs => ∃ ps, align cs tail vs = some ps ∧ ∀ p ∈ ps, p.1.T p.2)
      (fun vs => (align cs tail vs).bind (traverse fun cv => cv.1.e cv.2))
      (fun as => (align cs tail as).bind (traverse fun ca => ca.1.p ca.2)) := by
  refine Codec.ext ?_ rfl ?_ ?_ <;> funext v <;> cases v <;>
    simp [tupleCodec, carriedCodec, arrV, lA]

/-- (R) for the payload pair: realign the written row against the same codecs, then
    read back position by position. -/
theorem tuple_retract (hd : ∀ c ∈ cs, LawfulCore c) (htl : ∀ c ∈ tail, LawfulCore c) :
    ∀ vs as, (align cs tail vs).bind (traverse fun cv => cv.1.e cv.2) = some as →
      (align cs tail as).bind (traverse fun ca => ca.1.p ca.2) = some vs := by
  intro vs as hE
  obtain ⟨ps, hal, htr⟩ := Option.bind_eq_some_iff.mp hE
  obtain ⟨ds, hs, hlen, rfl⟩ := align_eq_some.mp hal
  have hn : as.length = vs.length := by
    rw [← traverse_length _ _ htr, List.length_zip, hlen, Nat.min_self]
  exact Option.bind_eq_some_iff.mpr ⟨_, align_of_slots hs hn,
    zip_roundTrip ds vs as (slots_all hd htl hs) hlen htr⟩

/-- A tuple is lawful: the alignment puts each position on its own codec. -/
theorem lawful_tupleCodec (hcs : ∀ c ∈ cs, Lawful c) (htl : ∀ c ∈ tail, Lawful c) :
    Lawful (tupleCodec cs tail) := by
  refine tupleCodec_eq ▸ lawful_carried (fun _ => rfl)
    (tuple_retract (fun c h => (hcs c h).core) (fun c h => (htl c h).core)) ?_
  intro as vs hD
  obtain ⟨ps, hal, htr⟩ := Option.bind_eq_some_iff.mp hD
  obtain ⟨ds, hs, hlen, rfl⟩ := align_eq_some.mp hal
  have hn : vs.length = as.length := by
    rw [← traverse_length _ _ htr, List.length_zip, hlen, Nat.min_self]
  rw [align_of_slots hs hn]
  exact zip_canonS ds as vs (slots_all hcs htl hs) hlen htr

theorem carrier_tupleCodec (hcs : ∀ c ∈ cs, Carrier c) (htl : ∀ c ∈ tail, Carrier c) :
    Carrier (tupleCodec cs tail) := by
  refine tupleCodec_eq ▸ carrier_carried ?_ ?_
  · intro vs as hE
    obtain ⟨ps, hal, htr⟩ := Option.bind_eq_some_iff.mp hE
    obtain ⟨ds, hs, hlen, rfl⟩ := align_eq_some.mp hal
    exact ⟨_, hal, zip_domE ds vs as (slots_all hcs htl hs) htr⟩
  · intro as vs hD
    obtain ⟨ps, hal, htr⟩ := Option.bind_eq_some_iff.mp hD
    obtain ⟨ds, hs, hlen, rfl⟩ := align_eq_some.mp hal
    have hn : vs.length = as.length := by
      rw [← traverse_length _ _ htr, List.length_zip, hlen, Nat.min_self]
    exact ⟨_, align_of_slots hs hn, zip_ranP ds as vs (slots_all hcs htl hs) htr⟩

end Tuple

/-! #### `list` (§3) — one prefix, at most one spread, one suffix

`list` is the positional product that `tuple` cannot state: a fixed **suffix** after a
spread, so `[A, B, ...C[], D]` has a term. The shape assigns a row of `n` codecs the same
way `tuple` does, and the extra content is one sentence: the last `|suf|` positions are
the suffix, and the first `n - |suf|` are exactly `tuple`'s row. So `slotsL` is `slots`
with the suffix appended, and every fact proved about `slots` carries over through that
one append. The four clauses of §2 then run position by position over the row, as they do
for `tuple` and for `array`.

`tuple` is the case with no suffix and `array` the case with no prefix and no suffix. Both
are proved equal to a `list` below rather than restated, so the positional theory is
proved one time. -/

/-- The codec row a `list` shape assigns to `n` positions: the prefix positionally, the
    spread as often as the middle needs, then the suffix. `none` is the length the shape
    refuses, which is every `n` below `|suf|`, and every `n` that `slots` then refuses. -/
def slotsL (pre : List Codec) (spread : Option Codec) (suf : List Codec) (n : Nat) :
    Option (List Codec) :=
  if n < suf.length then none
  else (slots pre spread (n - suf.length)).map (· ++ suf)

/-- `align` for a `list`: the row zipped with the positions, exactly as `align_eq_zip`
    shows `align` itself to be. -/
def alignL {α : Type} (pre : List Codec) (spread : Option Codec) (suf : List Codec)
    (xs : List α) : Option (List (Codec × α)) :=
  (slotsL pre spread suf xs.length).map (·.zip xs)

/-- A row the shape accepts has exactly the length asked of it. -/
theorem slotsL_length (pre : List Codec) (sp : Option Codec) (suf : List Codec) (n : Nat)
    (ds) (h : slotsL pre sp suf n = some ds) : ds.length = n := by
  unfold slotsL at h
  split at h
  · exact absurd h (by simp)
  · next hlt =>
    obtain ⟨ds', h', rfl⟩ := Option.map_eq_some_iff.mp h
    rw [List.length_append, slots_length pre sp (n - suf.length) ds' h']
    omega

/-- Every codec in the row is one the shape declared: a prefix position, the spread, or a
    suffix position. -/
theorem slotsL_mem (pre : List Codec) (sp : Option Codec) (suf : List Codec) (n : Nat)
    (ds) (h : slotsL pre sp suf n = some ds) :
    ∀ c ∈ ds, c ∈ pre ∨ sp = some c ∨ c ∈ suf := by
  unfold slotsL at h
  split at h
  · exact absurd h (by simp)
  · next hlt =>
    obtain ⟨ds', h', rfl⟩ := Option.map_eq_some_iff.mp h
    intro c hc
    rcases List.mem_append.mp hc with hc' | hc'
    · exact (slots_mem pre sp (n - suf.length) ds' h' c hc').imp id Or.inl
    · exact Or.inr (Or.inr hc')

/-- A property of the shape's three parts is a property of every codec in every row. -/
theorem slotsL_all {Q : Codec → Prop} {pre : List Codec} {sp : Option Codec}
    {suf : List Codec} (hpre : ∀ c ∈ pre, Q c) (hsp : ∀ c ∈ sp, Q c)
    (hsuf : ∀ c ∈ suf, Q c) {n ds} (hs : slotsL pre sp suf n = some ds) :
    ∀ c ∈ ds, Q c := fun c hc =>
  (slotsL_mem pre sp suf n ds hs c hc).elim (hpre c)
    (fun h => h.elim (fun he => hsp c he) (hsuf c))

/-- **The pivot for `alignL`**, and it says what `align_eq_some` says: which codec a
    position gets depends on the position alone, never on what stands there. -/
theorem alignL_eq_some {α : Type} {pre : List Codec} {sp : Option Codec} {suf : List Codec}
    {xs : List α} {ps} :
    alignL pre sp suf xs = some ps ↔
      ∃ ds, slotsL pre sp suf xs.length = some ds ∧ ds.length = xs.length ∧ ps = ds.zip xs := by
  unfold alignL
  constructor
  · intro h
    obtain ⟨ds, h', rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨ds, h', slotsL_length _ _ _ _ _ h', rfl⟩
  · rintro ⟨ds, h', _, rfl⟩
    rw [h']; rfl

/-- …so any row of the same length aligns against the same codecs. -/
theorem alignL_of_slotsL {α : Type} {pre : List Codec} {sp : Option Codec}
    {suf : List Codec} {n ds} (h : slotsL pre sp suf n = some ds) {xs : List α}
    (hn : xs.length = n) : alignL pre sp suf xs = some (ds.zip xs) := by
  unfold alignL; rw [hn, h]; rfl

/-- No suffix is `tuple`'s row, on the nose. -/
theorem slotsL_nil_suf (pre : List Codec) (sp : Option Codec) (n : Nat) :
    slotsL pre sp [] n = slots pre sp n := by
  unfold slotsL
  simp

/-- …and therefore `tuple`'s alignment. -/
theorem alignL_nil_suf {α : Type} (pre : List Codec) (sp : Option Codec) (xs : List α) :
    alignL pre sp [] xs = align pre sp xs := by
  unfold alignL
  rw [slotsL_nil_suf, align_eq_zip]

/-- A row the shape accepts splits at the suffix: `tuple`'s row for the positions before
    it, then the suffix itself. -/
theorem slotsL_split (pre : List Codec) (sp : Option Codec) (suf : List Codec) (n : Nat)
    (ds) (h : slotsL pre sp suf n = some ds) :
    ∃ dsF, slots pre sp (n - suf.length) = some dsF ∧ ds = dsF ++ suf
        ∧ dsF.length = n - suf.length ∧ suf.length ≤ n := by
  unfold slotsL at h
  split at h
  · exact absurd h (by simp)
  · next hlt =>
    obtain ⟨dsF, h', rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨dsF, h', rfl, slots_length _ _ _ _ h', by omega⟩

/-- **The split for `alignL`.** An alignment of a `list` is an alignment of its prefix and
    spread against the left part, and the suffix zipped with the right part. This is what
    lets every `align` fact serve the `list` unchanged. -/
theorem alignL_split {α : Type} (pre : List Codec) (sp : Option Codec) (suf : List Codec)
    (xs : List α) (ps) (h : alignL pre sp suf xs = some ps) :
    ∃ front back psF, xs = front ++ back ∧ back.length = suf.length
      ∧ align pre sp front = some psF ∧ ps = psF ++ suf.zip back := by
  obtain ⟨ds, hs, hlen, rfl⟩ := alignL_eq_some.mp h
  obtain ⟨dsF, hsF, rfl, hlenF, hle⟩ := slotsL_split pre sp suf xs.length ds hs
  refine ⟨xs.take (xs.length - suf.length), xs.drop (xs.length - suf.length),
    dsF.zip (xs.take (xs.length - suf.length)),
    (List.take_append_drop _ _).symm, by simp; omega,
    align_of_slots hsF (by simp), ?_⟩
  conv_lhs => rw [← List.take_append_drop (xs.length - suf.length) xs]
  rw [List.zip_append (by simp; omega)]



/-- …and the split built rather than read: a row long enough for the suffix aligns. -/
theorem alignL_of_split {α : Type} {pre : List Codec} {sp : Option Codec} {suf : List Codec}
    {front back : List α} {psF} (hb : back.length = suf.length)
    (h : align pre sp front = some psF) :
    alignL pre sp suf (front ++ back) = some (psF ++ suf.zip back) := by
  obtain ⟨ds, hs, hlen, rfl⟩ := align_eq_some.mp h
  unfold alignL slotsL
  rw [if_neg (by simp [hb]), show (front ++ back).length - suf.length = front.length by
    simp [hb], hs]
  simp only [Option.map_some]
  rw [List.zip_append (by omega)]

/-- A row shorter than the suffix aligns against nothing. -/
theorem alignL_short {α : Type} (pre : List Codec) (sp : Option Codec) (suf : List Codec)
    (xs : List α) (h : xs.length < suf.length) : alignL pre sp suf xs = none := by
  unfold alignL slotsL; rw [if_pos h]; rfl

/-- **`alignL` as one equation.** A row long enough for the suffix aligns exactly when its
    left part aligns against the prefix and spread, and the answer is that alignment with
    the suffix zipped onto the right part. Every fact about `alignL` follows from this and
    the corresponding fact about `align`. -/
theorem alignL_eq_split {α : Type} (pre : List Codec) (sp : Option Codec) (suf : List Codec)
    (xs : List α) (h : suf.length ≤ xs.length) :
    alignL pre sp suf xs
      = (align pre sp (xs.take (xs.length - suf.length))).map
          (· ++ suf.zip (xs.drop (xs.length - suf.length))) := by
  cases hal : align pre sp (xs.take (xs.length - suf.length)) with
  | none =>
    simp only [Option.map_none]
    cases hL : alignL pre sp suf xs with
    | none => rfl
    | some ps =>
      obtain ⟨front, back, psF, rfl, hblen, halF, rfl⟩ := alignL_split _ _ _ _ _ hL
      have hlen : (front ++ back).length - suf.length = front.length := by simp [hblen]
      rw [hlen, List.take_left] at hal
      rw [hal] at halF
      exact nomatch halF
  | some psF =>
    have hb : (xs.drop (xs.length - suf.length)).length = suf.length := by simp; omega
    have := alignL_of_split (pre := pre) (sp := sp) (suf := suf) hb hal
    rw [List.take_append_drop] at this
    rw [this]
    rfl

/-- §3 `(list)`: the positional product over a prefix, a spread and a suffix. -/
def listCodec (pre : List Codec) (spread : Option Codec) (suf : List Codec) : Codec :=
  { T := fun v => match v with
      | .arr vs => ∃ ps, alignL pre spread suf vs = some ps ∧ ∀ p ∈ ps, p.1.T p.2
      | _ => False
    μ := some .L
    e := fun v => match v with
      | .arr vs => ((alignL pre spread suf vs).bind
          (traverse fun cv => cv.1.e cv.2)).map Attr.l
      | _ => none
    p := fun a => match a with
      | .l as => ((alignL pre spread suf as).bind
          (traverse fun ca => ca.1.p ca.2)).map Value.arr
      | _ => none }

section ListShape
variable {pre : List Codec} {sp : Option Codec} {suf : List Codec}

/-- `list` is `carriedCodec` between the same two prisms as `tuple` and `array`. -/
theorem listCodec_eq :
    listCodec pre sp suf = carriedCodec arrV lA .L
      (fun vs => ∃ ps, alignL pre sp suf vs = some ps ∧ ∀ p ∈ ps, p.1.T p.2)
      (fun vs => (alignL pre sp suf vs).bind (traverse fun cv => cv.1.e cv.2))
      (fun as => (alignL pre sp suf as).bind (traverse fun ca => ca.1.p ca.2)) := by
  refine Codec.ext ?_ rfl ?_ ?_ <;> funext v <;> cases v <;>
    simp [listCodec, carriedCodec, arrV, lA]

/-- (R) for the payload pair: realign the written row against the same codecs, then read
    back position by position. -/
theorem list_retract (hpre : ∀ c ∈ pre, LawfulCore c) (hsp : ∀ c ∈ sp, LawfulCore c)
    (hsuf : ∀ c ∈ suf, LawfulCore c) :
    ∀ vs as, (alignL pre sp suf vs).bind (traverse fun cv => cv.1.e cv.2) = some as →
      (alignL pre sp suf as).bind (traverse fun ca => ca.1.p ca.2) = some vs := by
  intro vs as hE
  obtain ⟨ps, hal, htr⟩ := Option.bind_eq_some_iff.mp hE
  obtain ⟨ds, hs, hlen, rfl⟩ := alignL_eq_some.mp hal
  have hn : as.length = vs.length := by
    rw [← traverse_length _ _ htr, List.length_zip, hlen, Nat.min_self]
  exact Option.bind_eq_some_iff.mpr ⟨_, alignL_of_slotsL hs hn,
    zip_roundTrip ds vs as (slotsL_all hpre hsp hsuf hs) hlen htr⟩

/-- A list is lawful: the alignment puts each position on its own codec. -/
theorem lawful_listCodec (hpre : ∀ c ∈ pre, Lawful c) (hsp : ∀ c ∈ sp, Lawful c)
    (hsuf : ∀ c ∈ suf, Lawful c) : Lawful (listCodec pre sp suf) := by
  refine listCodec_eq ▸ lawful_carried (fun _ => rfl)
    (list_retract (fun c h => (hpre c h).core) (fun c h => (hsp c h).core)
      (fun c h => (hsuf c h).core)) ?_
  intro as vs hD
  obtain ⟨ps, hal, htr⟩ := Option.bind_eq_some_iff.mp hD
  obtain ⟨ds, hs, hlen, rfl⟩ := alignL_eq_some.mp hal
  have hn : vs.length = as.length := by
    rw [← traverse_length _ _ htr, List.length_zip, hlen, Nat.min_self]
  rw [alignL_of_slotsL hs hn]
  exact zip_canonS ds as vs (slotsL_all hpre hsp hsuf hs) hlen htr

/-- Writing and reading a `list` puts every position on its own carrier. -/
theorem carrier_listCodec (hpre : ∀ c ∈ pre, Carrier c) (hsp : ∀ c ∈ sp, Carrier c)
    (hsuf : ∀ c ∈ suf, Carrier c) : Carrier (listCodec pre sp suf) := by
  refine listCodec_eq ▸ carrier_carried ?_ ?_
  · intro vs as hE
    obtain ⟨ps, hal, htr⟩ := Option.bind_eq_some_iff.mp hE
    obtain ⟨ds, hs, hlen, rfl⟩ := alignL_eq_some.mp hal
    exact ⟨_, hal, zip_domE ds vs as (slotsL_all hpre hsp hsuf hs) htr⟩
  · intro as vs hD
    obtain ⟨ps, hal, htr⟩ := Option.bind_eq_some_iff.mp hD
    obtain ⟨ds, hs, hlen, rfl⟩ := alignL_eq_some.mp hal
    have hn : vs.length = as.length := by
      rw [← traverse_length _ _ htr, List.length_zip, hlen, Nat.min_self]
    exact ⟨_, alignL_of_slotsL hs hn, zip_ranP ds as vs (slotsL_all hpre hsp hsuf hs) htr⟩

end ListShape

/-- **`tuple` is the `list` with no suffix.** -/
theorem tupleCodec_eq_listCodec (cs : List Codec) (tail : Option Codec) :
    tupleCodec cs tail = listCodec cs tail [] := by
  refine Codec.ext ?_ rfl ?_ ?_ <;> funext v <;> cases v <;>
    simp [tupleCodec, listCodec, alignL_nil_suf]

/-- A spread alone assigns the same codec to every position. -/
theorem slots_spread (c : Codec) : ∀ n : Nat, slots [] (some c) n = some (List.replicate n c)
  | 0 => rfl
  | n + 1 => by rw [slots, slots_spread c n]; rfl

/-- Traversing a row of one repeated codec is traversing that codec. -/
theorem traverse_replicate_zip {α β : Type} (c : Codec) (g : Codec → α → Option β) :
    ∀ xs : List α,
      traverse (fun q : Codec × α => g q.1 q.2) ((List.replicate xs.length c).zip xs)
        = traverse (g c) xs
  | [] => rfl
  | x :: xs => by
      simp only [List.length_cons, List.replicate_succ, List.zip_cons_cons, traverse_cons]
      rw [traverse_replicate_zip c g xs]

/-- A spread alone aligns every position against the one codec. -/
theorem alignL_spread {α : Type} (c : Codec) (xs : List α) :
    alignL [] (some c) [] xs = some ((List.replicate xs.length c).zip xs) := by
  unfold alignL
  rw [slotsL_nil_suf, slots_spread]
  rfl

/-- A position of such an alignment is the codec paired with a member of the row. -/
theorem mem_replicate_zip {α : Type} (c : Codec) (xs : List α) (d : Codec) (x : α) :
    (d, x) ∈ (List.replicate xs.length c).zip xs ↔ d = c ∧ x ∈ xs := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := List.of_mem_zip h
    exact ⟨List.eq_of_mem_replicate h1, h2⟩
  · rintro ⟨rfl, h2⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp h2
    rw [List.mem_iff_getElem]
    exact ⟨i, by simp [hi], by simp [List.getElem_zip]⟩

/-- `array` writes what the `list` with one spread writes. -/
theorem arrayCodec_e (c : Codec) (v : Value) :
    (arrayCodec c).e v = (listCodec [] (some c) []).e v := by
  cases v <;> (simp only [arrayCodec, listCodec]; try rfl)
  rw [alignL_spread]
  show _ = ((traverse (fun q : Codec × Value => q.1.e q.2) _).map Attr.l)
  rw [traverse_replicate_zip c (fun d x => d.e x)]

/-- …and reads what it reads. -/
theorem arrayCodec_p (c : Codec) (a : Attr) :
    (arrayCodec c).p a = (listCodec [] (some c) []).p a := by
  cases a <;> (simp only [arrayCodec, listCodec]; try rfl)
  rw [alignL_spread]
  show _ = ((traverse (fun q : Codec × Attr => q.1.p q.2) _).map Value.arr)
  rw [traverse_replicate_zip c (fun d x => d.p x)]

/-- …and carries what it carries. -/
theorem arrayCodec_T (c : Codec) (v : Value) :
    (arrayCodec c).T v ↔ (listCodec [] (some c) []).T v := by
  cases v <;> (simp only [arrayCodec, listCodec]; try exact Iff.rfl)
  rw [alignL_spread]
  constructor
  · intro h
    refine ⟨_, rfl, fun p hp => ?_⟩
    obtain ⟨d, x⟩ := p
    obtain ⟨rfl, h2⟩ := (mem_replicate_zip c _ d x).mp hp
    exact h _ h2
  · rintro ⟨ps, hps, hall⟩
    cases hps
    intro x hx
    exact hall (c, x) ((mem_replicate_zip c _ c x).mpr ⟨rfl, hx⟩)

/-- **`array` is the `list` with one spread and nothing else.** `arrayCodec` keeps its own
    unfolded definition, because the `opaque` fixpoint reduces through it. -/
theorem arrayCodec_eq_listCodec (c : Codec) : arrayCodec c = listCodec [] (some c) [] :=
  Codec.ext (funext fun v => propext (arrayCodec_T c v)) rfl
    (funext (arrayCodec_e c)) (funext (arrayCodec_p c))

end

end Calculus
