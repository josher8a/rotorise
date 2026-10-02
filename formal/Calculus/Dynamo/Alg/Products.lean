import Calculus.Dynamo.Alg.Prisms
import Calculus.Alg.Containers

/-!
# Products

The traversal toolkit and the products built on it. `carriedCodec`, a payload map carried by
a prism, is the shape underneath all of them: `entrywise` is it at a traversal,
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

export Alg (setImage_eq setImage_inv setImage_none_of setImage_isSome_of
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

/-- The member a set stores, computed from its element's (§3 `(set)`). -/
def setMember : Member → Option Member
  | .S => some .SS
  | .N => some .NS
  | .B => some .BS
  | _ => none

/-- The member that each kind's element stamps: the member of its ground kind. -/
abbrev SetKind.member (k : SetKind) : Member := k.ground.member

/-- A datum with the kind's member is one that the element prism matches. -/
theorem SetKind.out_of_member {k : SetKind} {a : Attr} (h : a.member = k.member) :
    ∃ y, k.elem.out a = some y := by
  cases k <;> cases a <;> first | exact ⟨_, rfl⟩ | exact nomatch h

/-- The wire set of a kind stamps the set member of the kind's member. -/
theorem SetKind.wire_member (k : SetKind) (T : NEFinset k.Carrier) :
    setMember k.member = some (k.wire T).member := by
  cases k <;> rfl

/-- A member with a set member is the member of a kind. -/
theorem SetKind.of_setMember {μ₀ μS : Member} (h : setMember μ₀ = some μS) :
    ∃ k : SetKind, μ₀ = k.member := by
  cases μ₀
  case S => exact ⟨.string, rfl⟩
  case N => exact ⟨.number, rfl⟩
  case B => exact ⟨.binary, rfl⟩
  all_goals exact nomatch h

/-- **A set's payloads at an orientation, into one kind**: image each element through the codec
    at `o`, into the wire set of the kind `k`. -/
noncomputable def setAtK {α : Type} (o : Alg.Orient) (c : Codec) (inj : α → Attr)
    (S : NEFinset α) (k : SetKind) : Option Attr :=
  (neSetImage (fun x => (c.f o (inj x)).bind k.elem.out) S).map k.wire

/-- **A set's payloads at an orientation**: the wire set of the kind that the image selects. The
    write is the map at the host, and the read is the map at the dual. -/
noncomputable def setAt {α : Type} (o : Alg.Orient) (c : Codec) (inj : α → Attr) (S : NEFinset α) :
    Option Attr :=
  match setAtK o c inj S .string with
  | some a => some a
  | none => match setAtK o c inj S .number with
    | some a => some a
    | none => setAtK o c inj S .binary

/-! No emptiness guard here: §1 types the wire sets as `℘⁺fin`, which is a type, so there is
no empty set for a codec to refuse. -/

section SetAt
variable {α : Type} {o : Alg.Orient} {c : Codec} {inj : α → Attr} {S : NEFinset α} {a : Attr}

/-- What one kind produces: the wire set of the image. -/
theorem setAtK_eq {k : SetKind} : setAtK o c inj S k = some a ↔
    ∃ T, neSetImage (fun x => (c.f o (inj x)).bind k.elem.out) S = some T ∧ a = k.wire T := by
  simp [setAtK, Option.map_eq_some_iff, eq_comm]

/-- A move is the move of one kind. -/
theorem setAt_some (h : setAt o c inj S = some a) : ∃ k, setAtK o c inj S k = some a := by
  unfold setAt at h
  split at h
  · next a' ha => cases h; exact ⟨.string, ha⟩
  · split at h
    · next a' ha => cases h; exact ⟨.number, ha⟩
    · exact ⟨.binary, h⟩

/-- **A kind that moves the set, where every other kind misses, decides the move.** -/
theorem setAt_of {k : SetKind} (h : setAtK o c inj S k = some a)
    (hm : ∀ k', k' ≠ k → setAtK o c inj S k' = none) : setAt o c inj S = some a := by
  cases k
  · simp only [setAt, h]
  · simp only [setAt, h, hm .string (by decide)]
  · simp only [setAt, h, hm .string (by decide), hm .number (by decide)]

/-- Moving a set needs every element to move. -/
theorem setAt_elem (h : setAt o c inj S = some a) : ∀ x ∈ S.1, (c.f o (inj x)).isSome = true := by
  obtain ⟨k, hk⟩ := setAt_some h
  obtain ⟨T, hT, -⟩ := setAtK_eq.mp hk
  exact fun x hx => Option.isSome_of_isSome_bind (setImage_some (neSetImage_eq_setImage.mp hT) x hx)

/-- Two codecs that agree at the orientation on each element move one set. -/
theorem setAt_congr {d : Codec} (h : ∀ x ∈ S.1, c.f o (inj x) = d.f o (inj x)) :
    setAt o c inj S = setAt o d inj S := by
  have hk : ∀ k, setAtK o c inj S k = setAtK o d inj S k := fun k => by
    unfold setAtK
    rw [neSetImage_congr (S := S) (g := fun x => (d.f o (inj x)).bind k.elem.out)
      (fun x hx => by rw [h x hx])]
  simp only [setAt, hk]

/-- What a move produces: the wire set of one kind, each element the image of an element of the
    set. -/
theorem setAt_mem {v : Attr} (h : setAt o c inj S = some v) :
    ∃ (k : SetKind) (T : NEFinset k.Carrier), v = k.wire T ∧
      ∀ y ∈ T.1, ∃ x ∈ S.1, c.f o (inj x) = some (k.elem.into y) := by
  obtain ⟨k, hk⟩ := setAt_some h
  obtain ⟨T, hT, rfl⟩ := setAtK_eq.mp hk
  refine ⟨k, T, rfl, fun y hy => ?_⟩
  obtain ⟨x, hx, hxy⟩ := (mem_setImage (neSetImage_eq_setImage.mp hT) y).mp hy
  exact ⟨x, hx, k.elem.bind_out hxy⟩

end SetAt

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

/-! ### A codec carried by a prism

`carriedCodec` and `entrywise` take the carriers as parameters. The aliases give them their names
in this namespace. -/

export Alg (carriedCodec carried_e lawful_carried carrier_carried entrywise lawful_entrywise
  carrier_entrywise)

/-! ### `array` (§3) — entrywise at `L` -/

/-! ### What `set` moves

    A set is a choice among three wire constructors rather than one prism, which is why it is
    not an `entrywise` product and why its inversion names all three families. -/

/-- What `set` moves at an orientation: the wire set of one kind, its payloads imaged through
    the element codec. -/
theorem setCodec_f_eq {c : Codec} {o : Alg.Orient} {x y : Attr} :
    (setCodec c).f o x = some y ↔
      ∃ (k : SetKind) (S : NEFinset k.Carrier), x = k.wire S ∧ setAt o c k.elem.into S = some y := by
  constructor
  · intro h
    cases x
    case ss S => exact ⟨.string, S, rfl, h⟩
    case ns S => exact ⟨.number, S, rfl, h⟩
    case bs S => exact ⟨.binary, S, rfl, h⟩
    all_goals exact nomatch h
  · rintro ⟨k, S, rfl, h⟩
    cases k <;> exact h

/-- What `set` moves at the wire set of a kind: the set through the kind's element prism. -/
theorem setCodec_wire_f {c : Codec} {o : Alg.Orient} {k : SetKind} {S : NEFinset k.Carrier} :
    (setCodec c).f o (k.wire S) = setAt o c k.elem.into S := by
  cases k <;> rfl

/-- What `set` holds at the wire set of a kind: every element is held. -/
theorem setCodec_T_wire {c : Codec} {k : SetKind} {S : NEFinset k.Carrier} :
    (setCodec c).T (k.wire S) ↔ ∀ x ∈ S.1, c.T (k.elem.into x) := by
  cases k <;> exact Iff.rfl

/-- §3 `array`: the list former with a spread and no fixed positions. -/
abbrev arrayCodec (c : Codec) : Codec := Alg.listCodec lS [] (some c) []

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
    simp only [lS, lA] at hys; cases hys
    rw [Alg.alignL_spread] at hal; cases hal
    exact hps (c, x) ((Alg.mem_replicate_zip _ _ _ x).mpr ⟨rfl, hx⟩)
  · intro h
    refine ⟨xs, rfl, _, Alg.alignL_spread c xs, fun p hp => ?_⟩
    obtain ⟨d, x⟩ := p
    obtain ⟨rfl, hx⟩ := (Alg.mem_replicate_zip c xs d x).mp hp
    exact h x hx

theorem lawful_arrayCodec {c : Codec} (h : Lawful c) : Lawful (arrayCodec c) :=
  Alg.lawful_listCodec (fun _ h => nomatch h) (fun _ hc => by cases hc; exact h)
    (fun _ h => nomatch h)

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
  Alg.listCodec lS pre spread suf

section ListShape
variable {pre : List Codec} {sp : Option Codec} {suf : List Codec}

end ListShape

/-- **§3 `tuple` is the `list` with no suffix.** -/
abbrev tupleCodec (cs : List Codec) (tail : Option Codec) : Codec := listCodec cs tail []

end

end Calculus
