import Calculus.Dynamo.Alg.Prisms
import Calculus.Alg.Containers

/-!
# Products

The traversal toolkit and the products built on it. `carriedCodec`, a payload pair carried
between two prisms, is the shape underneath all of them: `entrywise` is it at a traversal,
hence `arrayCodec` and `recordCodec`, and `tupleCodec` is it at `align` plus a traversal,
where the one fact worth proving is that alignment depends on a row's *length* alone.
`setCodec` is argued on its own.

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

/-- A `bind` through a prism pins the datum. -/
theorem bind_sC {o : Option Value} {y : String} (h : o.bind sC.out = some y) :
    o = some (.str y) := by
  cases o with
  | none => exact nomatch h
  | some w => cases w <;> simp_all [sC]

theorem bind_nC {o : Option Value} {y : WFNumeral} (h : o.bind nC.out = some y) :
    o = some (.num y) := by
  cases o with
  | none => exact nomatch h
  | some w => cases w <;> simp_all [nC]

theorem bind_bC {o : Option Value} {y : Bytes} (h : o.bind bC.out = some y) :
    o = some (.bin y) := by
  cases o with
  | none => exact nomatch h
  | some w => cases w <;> simp_all [bC]

/-- The member a set stores, computed from its element's (§3 `(set)`). -/
def setMember : Member → Option Member
  | .S => some .SS
  | .N => some .NS
  | .B => some .BS
  | _ => none

/-- **A set's payloads at an orientation**: image each element through the codec at `o`, into the
    wire set that the image selects. The write is the map at the host, and the read is the map at
    the dual. -/
noncomputable def setAt {α : Type} (o : Alg.Orient) (c : Codec) (inj : α → Attr) (S : NEFinset α) :
    Option Attr :=
  match neSetImage (fun x => (c.f o (inj x)).bind sC.out) S with
  | some T => some (.ss T)
  | none => match neSetImage (fun x => (c.f o (inj x)).bind nC.out) S with
    | some T => some (.ns T)
    | none => (neSetImage (fun x => (c.f o (inj x)).bind bC.out) S).map Attr.bs

/-! No emptiness guard here: §1 types the wire sets as `℘⁺fin`, which is a type, so there is
no empty set for a codec to refuse. -/

/-- Moving a set needs every element to move. -/
theorem setAt_elem {α : Type} {o : Alg.Orient} {c : Codec} {inj : α → Attr} {S : NEFinset α}
    {a : Attr} (h : setAt o c inj S = some a) : ∀ x ∈ S.1, (c.f o (inj x)).isSome = true := by
  unfold setAt at h
  split at h
  · next T hT =>
      exact fun x hx => Option.isSome_of_isSome_bind (setImage_some (neSetImage_eq_setImage.mp hT) x hx)
  · split at h
    · next T hT =>
        exact fun x hx => Option.isSome_of_isSome_bind (setImage_some (neSetImage_eq_setImage.mp hT) x hx)
    · next =>
      obtain ⟨T, hT, -⟩ := Option.map_eq_some_iff.mp h
      exact fun x hx => Option.isSome_of_isSome_bind (setImage_some (neSetImage_eq_setImage.mp hT) x hx)

/-- Two codecs that agree at the orientation on each element move one set. -/
theorem setAt_congr {α : Type} {o : Alg.Orient} {c d : Codec} {inj : α → Attr} {S : NEFinset α}
    (h : ∀ x ∈ S.1, c.f o (inj x) = d.f o (inj x)) : setAt o c inj S = setAt o d inj S := by
  unfold setAt
  rw [neSetImage_congr (S := S) (g := fun x => (d.f o (inj x)).bind sC.out)
      (fun x hx => by rw [h x hx]),
    neSetImage_congr (S := S) (g := fun x => (d.f o (inj x)).bind nC.out)
      (fun x hx => by rw [h x hx]),
    neSetImage_congr (S := S) (g := fun x => (d.f o (inj x)).bind bC.out)
      (fun x hx => by rw [h x hx])]

/-- What a move produces: one of the three wire sets, each element the image of an element of
    the set. -/
theorem setAt_mem {α : Type} {o : Alg.Orient} {c : Codec} {inj : α → Attr} {S : NEFinset α}
    {v : Attr} (h : setAt o c inj S = some v) :
    (∃ T : NEFinset String, v = .ss T ∧
        ∀ y ∈ T.1, ∃ x ∈ S.1, c.f o (inj x) = some (.s y))
  ∨ (∃ T : NEFinset WFNumeral, v = .ns T ∧
        ∀ y ∈ T.1, ∃ x ∈ S.1, c.f o (inj x) = some (.n y))
  ∨ (∃ T : NEFinset Bytes, v = .bs T ∧
        ∀ y ∈ T.1, ∃ x ∈ S.1, c.f o (inj x) = some (.b y)) := by
  unfold setAt at h
  split at h
  · next T hT =>
    injection h with h
    refine Or.inl ⟨T, h.symm, fun y hy => ?_⟩
    obtain ⟨x, hx, hxy⟩ := (mem_setImage (neSetImage_eq_setImage.mp hT) y).mp hy
    exact ⟨x, hx, bind_sC hxy⟩
  · split at h
    · next T hT =>
      injection h with h
      refine Or.inr (Or.inl ⟨T, h.symm, fun y hy => ?_⟩)
      obtain ⟨x, hx, hxy⟩ := (mem_setImage (neSetImage_eq_setImage.mp hT) y).mp hy
      exact ⟨x, hx, bind_nC hxy⟩
    · next =>
      obtain ⟨T, hT, hv⟩ := Option.map_eq_some_iff.mp h
      refine Or.inr (Or.inr ⟨T, hv.symm, fun y hy => ?_⟩)
      obtain ⟨x, hx, hxy⟩ := (mem_setImage (neSetImage_eq_setImage.mp hT) y).mp hy
      exact ⟨x, hx, bind_bC hxy⟩

/-- §3 `(set)`. Non-emptiness, uniqueness and homogeneity are all carried by the **types**:
    a `Finset` has no repeats and no order, `℘⁺fin` has no empty inhabitant, and the three
    constructors are the three element types the reference names. What is left for the
    codec is the element map — and that is the whole of `(set)` now. -/
noncomputable def setCodec (c : Codec) : Codec where
  T v := match v with
    | .ss S => ∀ s ∈ S.1, c.T (.s s)
    | .ns S => ∀ d ∈ S.1, c.T (.n d)
    | .bs S => ∀ b ∈ S.1, c.T (.b b)
    | _ => False
  μ := c.μ.bind setMember
  f o x := match x with
    | .ss S => setAt o c Attr.s S
    | .ns S => setAt o c Attr.n S
    | .bs S => setAt o c Attr.b S
    | _ => none

/-! ### A codec carried between two prisms

`carriedCodec` and `entrywise` take the carriers as parameters. The aliases give them their names
in this namespace. -/

export Alg (carriedCodec carried_e lawful_carried carrier_carried entrywise lawful_entrywise
  carrier_entrywise)

/-! ### `array` (§3) — entrywise at `L` -/

/-! ### What `set` moves

    A set is a choice among three wire constructors rather than one prism, which is why it is
    not an `entrywise` product and why its inversion names all three families. -/

/-- What `set` moves at an orientation: one of the three wire sets, its payloads imaged through
    the element codec. -/
theorem setCodec_f_eq {c : Codec} {o : Alg.Orient} {x y : Attr} :
    (setCodec c).f o x = some y ↔
      (∃ S : NEFinset String, x = .ss S ∧ setAt o c Attr.s S = some y)
      ∨ (∃ S : NEFinset WFNumeral, x = .ns S ∧ setAt o c Attr.n S = some y)
      ∨ (∃ S : NEFinset Bytes, x = .bs S ∧ setAt o c Attr.b S = some y) := by
  cases x <;> simp [setCodec]

/-- §3 `array`: the list former with a spread and no fixed positions. -/
abbrev arrayCodec (c : Codec) : Codec := Alg.listCodec lA lA .L [] (some c) []

/-- **An array moves entry by entry**, at each orientation. -/
theorem arrayCodec_f (o : Alg.Orient) (c : Codec) (xs : List Attr) :
    (arrayCodec c).f o (.l xs) = (traverse (c.f o) xs).map Attr.l := by
  rcases o with ⟨⟨_ | _, _ | _⟩, ho⟩
  · exact absurd rfl ho
  · show (((lA.out (.l xs)).bind fun ys => (Alg.alignL [] (some c) [] ys).bind
        (traverse fun cv => cv.1.f _ cv.2)).map lA.into) = _
    simp only [lA, Option.bind_some]
    rw [Alg.alignL_spread]; simp only [Option.bind_some]
    rw [Alg.traverse_replicate_zip c (fun d x => d.f _ x)]
  · show (((lA.out (.l xs)).bind fun ys => (Alg.alignL [] (some c) [] ys).bind
        (traverse fun cv => cv.1.f _ cv.2)).map lA.into) = _
    simp only [lA, Option.bind_some]
    rw [Alg.alignL_spread]; simp only [Option.bind_some]
    rw [Alg.traverse_replicate_zip c (fun d x => d.f _ x)]
  · exact absurd rfl ho

/-- **An array holds a list whose every entry the element holds.** -/
theorem arrayCodec_T (c : Codec) (xs : List Attr) :
    (arrayCodec c).T (.l xs) ↔ ∀ x ∈ xs, c.T x := by
  constructor
  · rintro ⟨ys, hys, ps, hal, hps⟩ x hx
    simp only [lA] at hys; cases hys
    rw [Alg.alignL_spread] at hal; cases hal
    exact hps (c, x) ((Alg.mem_replicate_zip _ _ _ x).mpr ⟨rfl, hx⟩)
  · intro h
    refine ⟨xs, rfl, _, Alg.alignL_spread c xs, fun p hp => ?_⟩
    obtain ⟨d, x⟩ := p
    obtain ⟨rfl, hx⟩ := (Alg.mem_replicate_zip c xs d x).mp hp
    exact h x hx

theorem lawful_arrayCodec {c : Codec} (h : Lawful c) : Lawful (arrayCodec c) :=
  Alg.lawful_listCodec (fun _ => rfl) (fun _ h => nomatch h) (fun _ hc => by cases hc; exact h)
    (fun _ h => nomatch h)

theorem carrier_arrayCodec {c : Codec} (hc : Carrier c) : Carrier (arrayCodec c) :=
  Alg.carrier_listCodec (fun _ h => nomatch h) (fun _ h => by cases h; exact hc) (fun _ h => nomatch h)

/- The positional theory takes the carriers as parameters. The aliases give it its names in this
   namespace. -/
export Alg (align slots_all align_eq_some align_of_slots zip_canonS zip_domE zip_ranP
  tuple_retract alignL alignL_nil_suf alignL_of_split traverse_replicate_zip
  alignL_spread mem_replicate_zip)


/-! #### `list` (§3) — one prefix, at most one spread, one suffix

`list` is the positional product that `tuple` cannot state: a fixed **suffix** after a
spread, so `[A, B, ...C[], D]` has a term. The shape assigns a row of `n` codecs the same
way `tuple` does, and the extra content is one sentence: the last `|suf|` positions are
the suffix, and the first `n - |suf|` are exactly `tuple`'s row. So `slotsL` is `slots`
with the suffix appended, and every fact proved about `slots` carries over through that
one append. The four clauses of §2 then run position by position over the row, as they do
for `tuple` and for `array`.

`tuple` is the case with no suffix and `array` the case with no prefix and no suffix. Both
are defined as a `list`, so the positional theory is proved one time. -/

/-- §3 `(list)`: the positional product over a prefix, a spread and a suffix. The generic
    `list` at the `L` prism. -/
abbrev listCodec (pre : List Codec) (spread : Option Codec) (suf : List Codec) : Codec :=
  Alg.listCodec lA lA .L pre spread suf

section ListShape
variable {pre : List Codec} {sp : Option Codec} {suf : List Codec}

/-- `list` is `carriedCodec` between the same two prisms as `tuple` and `array`. -/
theorem listCodec_eq :
    listCodec pre sp suf = carriedCodec lA lA .L
      (fun vs => ∃ ps, alignL pre sp suf vs = some ps ∧ ∀ p ∈ ps, p.1.T p.2)
      (fun vs => (alignL pre sp suf vs).bind (traverse fun cv => cv.1.e cv.2))
      (fun as => (alignL pre sp suf as).bind (traverse fun ca => ca.1.p ca.2)) := rfl

end ListShape

/-- **§3 `tuple` is the `list` with no suffix.** -/
abbrev tupleCodec (cs : List Codec) (tail : Option Codec) : Codec := listCodec cs tail []

end

end Calculus
