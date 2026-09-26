import Calculus.Dynamo.Alg.Prisms
import Calculus.Alg.Containers

/-!
# Products

The traversal toolkit and the products built on it. `carriedCodec`, a payload pair carried
between two prisms, is the shape underneath all of them: `entrywise` is it at a traversal,
hence `arrayCodec` and `recordCodec`, and `tupleCodec` is it at `align` plus a traversal,
where the one fact worth proving is that alignment depends on a row's *length* alone.
`setCodec` is argued on its own. `drop` is a *filter* and not a traversal mode, so nothing
here needs a second toolkit.

`traverse`, `carriedCodec`, `entrywise`, `setImage`, and the alignment of a positional row take
the carriers as parameters, so they live in the generic layer. This file instantiates them at the
DynamoDB carriers.
-/

namespace Calculus

noncomputable section
/-! ## Filter facts (the sum proofs consume these) -/


/-! ## Products -/

export Alg (setImage setImage_some mem_setImage setImage_nonempty)

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

export Alg (setImage_eq setImage_inv setImage_roundTrip setImage_none_of setImage_isSome_of
  setImage_congr)

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

`carriedCodec` and `entrywise` take the carriers as parameters. The aliases give them their names
in this namespace. -/

export Alg (carriedCodec carried_e lawful_carried carrier_carried entrywise lawful_entrywise
  carrier_entrywise)

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

/- The positional theory takes the carriers as parameters. The aliases give it its names in this
   namespace. -/
export Alg (align slots slots_all align_eq_some align_of_slots zip_canonS zip_domE zip_ranP
  tuple_retract slotsL alignL alignL_nil_suf alignL_split alignL_of_split traverse_replicate_zip
  alignL_spread mem_replicate_zip)

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

/-- §3 `(list)`: the positional product over a prefix, a spread and a suffix. The generic
    `list` at the `arr` and `L` prisms. -/
abbrev listCodec (pre : List Codec) (spread : Option Codec) (suf : List Codec) : Codec :=
  Alg.listCodec arrV lA .L pre spread suf

section ListShape
variable {pre : List Codec} {sp : Option Codec} {suf : List Codec}

/-- `list` is `carriedCodec` between the same two prisms as `tuple` and `array`. -/
theorem listCodec_eq :
    listCodec pre sp suf = carriedCodec arrV lA .L
      (fun vs => ∃ ps, alignL pre sp suf vs = some ps ∧ ∀ p ∈ ps, p.1.T p.2)
      (fun vs => (alignL pre sp suf vs).bind (traverse fun cv => cv.1.e cv.2))
      (fun as => (alignL pre sp suf as).bind (traverse fun ca => ca.1.p ca.2)) := rfl

/-- A list is lawful: the alignment puts each position on its own codec. -/
theorem lawful_listCodec (hpre : ∀ c ∈ pre, Lawful c) (hsp : ∀ c ∈ sp, Lawful c)
    (hsuf : ∀ c ∈ suf, Lawful c) : Lawful (listCodec pre sp suf) :=
  Alg.lawful_listCodec (fun _ => rfl) hpre hsp hsuf

/-- Writing and reading a `list` puts every position on its own carrier. -/
theorem carrier_listCodec (hpre : ∀ c ∈ pre, Carrier c) (hsp : ∀ c ∈ sp, Carrier c)
    (hsuf : ∀ c ∈ suf, Carrier c) : Carrier (listCodec pre sp suf) :=
  Alg.carrier_listCodec hpre hsp hsuf

end ListShape

/-- **`tuple` is the `list` with no suffix.** -/
theorem tupleCodec_eq_listCodec (cs : List Codec) (tail : Option Codec) :
    tupleCodec cs tail = listCodec cs tail [] := by
  refine Codec.ext ?_ rfl ?_ ?_ <;> funext v <;> cases v <;>
    simp [tupleCodec, listCodec, Alg.listCodec, carriedCodec, arrV, lA, alignL_nil_suf]

/-- `array` writes what the `list` with one spread writes. -/
theorem arrayCodec_e (c : Codec) (v : Value) :
    (arrayCodec c).e v = (listCodec [] (some c) []).e v := by
  cases v <;> (simp only [arrayCodec, listCodec, Alg.listCodec, carriedCodec, arrV, lA,
      Option.bind_some]; try rfl)
  rw [alignL_spread]
  show _ = ((traverse (fun q : Codec × Value => q.1.e q.2) _).map Attr.l)
  rw [traverse_replicate_zip c (fun d x => d.e x)]

/-- …and reads what it reads. -/
theorem arrayCodec_p (c : Codec) (a : Attr) :
    (arrayCodec c).p a = (listCodec [] (some c) []).p a := by
  cases a <;> (simp only [arrayCodec, listCodec, Alg.listCodec, carriedCodec, arrV, lA,
      Option.bind_some]; try rfl)
  rw [alignL_spread]
  show _ = ((traverse (fun q : Codec × Attr => q.1.p q.2) _).map Value.arr)
  rw [traverse_replicate_zip c (fun d x => d.p x)]

/-- …and carries what it carries. -/
theorem arrayCodec_T (c : Codec) (v : Value) :
    (arrayCodec c).T v ↔ (listCodec [] (some c) []).T v := by
  cases v <;> (simp only [arrayCodec, listCodec, Alg.listCodec, carriedCodec, arrV, lA,
      Value.arr.injEq, reduceCtorEq,
    false_and, exists_false, exists_eq_left', iff_self]; try exact Iff.rfl)
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
