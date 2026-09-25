import Calculus.ExactA

/-!
# Orthogonality — occupancy and separation

`Obligations (.union opts)` carries pairwise compatibility. Two separated options are compatible
(`pairwiseCompat_of_separated`). The decidable certificate is `certPair` (`Meet.lean`): two
options are orthogonal when their meet is the bottom, when the meets of their two views are, or
when their occupancies are disjoint on both sides. The meet refuses a closure and the occupancies
read no predicate, so the slot test certifies a pair that the meet cannot state.
This module holds what the meet reads and what the certificate proves: the occupancies, the slot
test `Orth1` that the proofs of the meet's bottom rows use and the certificate uses alone, and
`Separates`.

## Sound, never complete, and why there is no `unknown`

Semantic orthogonality is undecidable in this language — `refine t q` carries an arbitrary
`Value → Bool` and `held t P f g` an arbitrary pair of maps. So the certificate answers a
*narrower* question, and the answer `false` means "no certificate", never "not orthogonal".

The direction that keeps this sound is that **over-approximating an occupancy is always
safe**: if `X ⊆ X'`, `Y ⊆ Y'` and `X' ∩ Y' = ∅`, then `X ∩ Y = ∅`. So an opaque subterm
contributes `⊤` — every slot — and a pair involving it simply fails to be certified. There is
no third truth value to introduce.

## Both halves of the pair

`Separates` takes **two** families, one over `Value` and one over `Attr`, and asks each to be
pairwise disjoint. A pair can be separated on one side and not on the other, and then it is not
separated. `held` is the witness: its write occupancy is its caller-side term's, and its read
occupancy is its stored-side term's. So `union(held(string, number, f, g), string)`, the decimal
adapter against a string, separates on the write side and meets on the read side.

The two sides coincide below `opaque`: under `HF`, `occA_le_occV` puts the read occupancy inside
the write occupancy under `Member.slot`, so a held-free pair disjoint on the write side is
disjoint on the read side.

## The write-side slot is the `Value` constructor, not `Kind`

`Kind` collapses `strSet`, `numSet` and `binSet` to `.set`, so `κ (set string)` and
`κ (set number)` are equal. The ten `Value` constructors can tell them apart, and `Adm (.set b)`
is exact, so the sharper partition is *available in the model*: the row for `set b` matches the
payload's wire family and asks `b.adm` of its elements, and `℘⁺fin` has no empty inhabitant, so
a base admits exactly one family. `Slot` below is that partition. The read-side slot is
`Member`, which `Attr.member` already computes.
-/

namespace Calculus

/-! ## Slots

`Slot` is the `Value` constructor as data. `Member` is reused unchanged for the read side —
`Attr.member` is already the constructor tag there.

**`Slot` and `Member` are in bijection**: the ten slots match the ten members one for one.

The two types are kept apart anyway, and deliberately, because the bijection is a FACT ABOUT
THE PRESENT TABLE rather than a property of the design. A slot is what a value is built with
and a member is what the store files it under; nothing makes them the same kind of thing, and
an adapter that gives a host carrier its own slot would part them again. Merging them is a
change to make on purpose, with the reason written down, and not by noticing they line up. -/

inductive Slot where
  | str | num | bool | bin | null | strSet | numSet | binSet | arr | map
deriving DecidableEq, Repr

/-- The constructor a value is built with. Ten of them, where `Value.kind` has eight. -/
def Value.slot : Value → Slot
  | .str _    => .str
  | .num _    => .num
  | .bool _   => .bool
  | .bin _    => .bin
  | .null     => .null
  | .strSet _ => .strSet
  | .numSet _ => .numSet
  | .binSet _ => .binSet
  | .arr _    => .arr
  | .map _ _  => .map

/-- Enumerations, so the disjointness test is a `List.all` rather than a `Fintype` instance —
    `decide` over these is the whole of what makes `Orth1` checkable by `by decide`. -/
def Slot.all : List Slot :=
  [.str, .num, .bool, .bin, .null, .strSet, .numSet, .binSet, .arr, .map]

theorem Slot.mem_all (s : Slot) : s ∈ Slot.all := by cases s <;> simp [Slot.all]

def Member.all : List Member := [.S, .N, .B, .BOOL, .NULL, .SS, .NS, .BS, .L, .M]

theorem Member.mem_all (m : Member) : m ∈ Member.all := by cases m <;> simp [Member.all]

/-- A literal base's *value* slot, as against `GroundKind.member`, its stored member. -/
def GroundKind.slot : GroundKind → Slot
  | .string  => .str
  | .number  => .num
  | .boolean => .bool
  | .binary  => .bin
  | .null    => .null

/-- A set base's value slot — the wire family its payload sits in. One slot for each base. -/
def SetBase.slot : SetBase → Slot
  | .string  => .strSet
  | .number  => .numSet
  | .binary  => .binSet

/-- The slot a member's values are built with: the bijection above, as a function. -/
def Member.slot : Member → Slot
  | .S => .str | .N => .num | .B => .bin | .BOOL => .bool | .NULL => .null
  | .SS => .strSet | .NS => .numSet | .BS => .binSet | .L => .arr | .M => .map

/-! ## Occupancy

An occupancy is a total map from slot to `Bool` — the three-element lattice `∅ | only s | ⊤`
with no separate representation, since a `Slot → Bool` is already the powerset and the
lattice operations are `||` and `&&`.

Computed from **one** term, never from a pair. A pairwise case analysis would be `n²` over
twenty-one constructors; this is `n`, and the pair only ever compares two answers. -/

def occOnly {α : Type} [DecidableEq α] (x : α) : α → Bool := fun y => decide (y = x)
def occTop {α : Type} : α → Bool := fun _ => true
def occNone {α : Type} : α → Bool := fun _ => false
def occWith {α : Type} [DecidableEq α] (x : α) (o : α → Bool) : α → Bool :=
  fun y => decide (y = x) || o y

mutual

/-- **Which value constructors this term can write.** An over-approximation of
    `{v.slot | Adm t v}`, and `occV_sound` is that containment.

    The `⊤` rows, and why each is `⊤` rather than sharper — §5's occupancy paragraph names
    the same terms:

    * `held t P f _` is no `⊤` row. `f` can move a value into any constructor, but the
      caller-side term `P` restricts what the held writes, so the write occupancy is `P`'s.
      The read occupancy is the stored-side term's (`occA`), which is another coordinate.
    * `refine t q` — the subterm's, over-approximating away `q`. Sound: a refinement writes
      a subset of what the base writes.
    * An alternate reader (`Codec.extendRead`) is outside the structural occupancy.
    * `opaq` — every slot, because `opaque` writes every value (`opaq_total`).
    * `union opts` — the union of the options'. A union admits only where one of its options
      admits, so the union of the options' occupancies is an over-approximation. -/
def occV : Term → Slot → Bool
  | .string  => occOnly .str
  | .number  => occOnly .num
  | .boolean => occOnly .bool
  | .binary  => occOnly .bin
  | .null    => occOnly .null
  | .literal k _ => occOnly k.slot
  -- the bottom writes nothing, so it occupies no slot
  | .never       => occNone
  | .set b       => occOnly b.slot
  -- `array` and `tuple` are one shape now, and both rows said the same thing
  | .list _ _ _  => occOnly .arr
  | .object _   => occOnly .map
  | .held _ P _ _ => occV P
  | .refine t _  => occV t
  | .union opts  => occVL opts
  | .opaq  => occTop
  -- a closed variable is the bottom, and a recursive term writes where its body does: its
  -- variable sits under a container, whose slot is the container's
  | .var _ => occNone
  | .mu b => occV b

def occVL : List Term → Slot → Bool
  | [] => fun _ => false
  | t :: ts => fun s => occV t s || occVL ts s
end

mutual

/-- **Which members this term can read.** The mirror, and it is not a symmetric mirror:
    `held` has distinct write and read rows.

    An alternate reader is a codec, not a `Term`. The occupancy has no alternate-reader
    row. -/
def occA : Term → Member → Bool
  | .string  => occOnly .S
  | .number  => occOnly .N
  | .boolean => occOnly .BOOL
  | .binary  => occOnly .B
  | .null    => occOnly .NULL
  | .literal k _ => occOnly k.member
  -- and stores nothing, so it occupies no member
  | .never       => occNone
  | .set b       => occOnly b.member
  | .list _ _ _  => occOnly .L
  | .object _   => occOnly .M
  | .refine t _  => occA t
  | .held t _ _ _ => occA t
  | .union opts  => occAL opts
  | .opaq  => occTop
  | .var _ => occNone
  | .mu b => occA b

def occAL : List Term → Member → Bool
  | [] => fun _ => false
  | t :: ts => fun m => occA t m || occAL ts m
end

/-! ## The slot test -/

/-- **The slot test**: the write occupancies disjoint, and the read occupancies disjoint. The
    certificate asks it as its third disjunct, because the meet refuses a closure and the
    occupancies read no predicate.

    **Two questions, and they coincide below `opaque`.** A `held` has its two occupancies in
    two coordinates: the write side is the caller-side term's, and the read side is the
    stored-side term's. A held-free term has one coordinate, and there the read occupancy
    lies inside the write occupancy (`occA_le_occV`, under `HF`). -/
def Orth1 (x y : Term) : Bool :=
  Slot.all.all (fun s => !(occV x s && occV y s)) &&
    Member.all.all (fun m => !(occA x m && occA y m))

/-! ## Soundness

The statement is about the **rows** (`Adm`/`AdmA`), and the proof is about open terms, because a
recursive term's occupancy is its body's. A term either writes a value in its own occupancy, or
one of its variables that reads the term's own input writes it (`occV_open`). A closed term has
no such variable, so the row lands in the occupancy (`occV_sound`). A body reads its variable
under a container, whose occupancy is the container's slot, so the occupancy of `mu b` is the
occupancy of `b` with the variable at no slot. This needs no guard: a stage that writes a value
writes it through the body at the stage before, and the stages start at the bottom. -/

def OccSoundV (t : Term) : Prop := ∀ v, Adm t v = true → occV t v.slot = true

/-- An occupancy of an option is inside the occupancy of the union. -/
theorem occVL_cons {t : Term} {ts : List Term} {s : Slot} (h : occV t s = true ∨ occVL ts s = true) :
    occVL (t :: ts) s = true := by
  rcases h with h | h <;> simp [occVL, h]

mutual

/-- **The write occupancy contains what an open term writes**, or a variable that reads the
    term's own input writes it. `set b` is where nonemptiness of `℘⁺fin` does the work: a set
    row matches all three wire families and asks `b.adm` element by element, so `set number`
    faced a `strSet` answers `∀ s ∈ S, inD (.str s)` — and `S` has an element, whose answer is
    `false`. -/
theorem occV_open : ∀ (t : Term) (ρ : List Codec) (v : Value),
    ((denote t ρ).e v).isSome = true →
      occV t v.slot = true ∨ ∃ i, 2 ≤ t.use i ∧ ((envAt ρ i).e v).isSome = true
  | .string, _, v, h | .boolean, _, v, h | .binary, _, v, h | .null, _, v, h
  | .number, _, v, h => Or.inl (by
      cases v <;> simp_all [denote, stringCodec, booleanCodec, binaryCodec, nullCodec,
        numberCodec, occV, occOnly, Value.slot])
  | .never, _, _, h => by simp [denote, Codec.empty] at h
  | .opaq, _, _, _ => Or.inl rfl
  | .literal k x, _, v, h => by
      have h := (Adm_exact (.literal k x) v).mpr h
      rw [Adm_literal] at h
      exact Or.inl (by
        cases k <;> cases v <;>
          simp_all [AdmLit, inL, occV, occOnly, Value.slot, GroundKind.slot])
  | .set b, _, v, h => by
      have h := (Adm_exact (.set b) v).mpr h
      refine Or.inl ?_
      cases v with
      | strSet S => obtain ⟨x, hx⟩ := S.2; cases b <;>
          simp_all [Adm, SetBase.adm, inD, occV, occOnly, Value.slot, SetBase.slot]
      | numSet S =>
          obtain ⟨x, hx⟩ := S.2
          have hnone : ∀ b' : SetBase, b'.adm (.num x) = false →
              Adm (.set b') (.numSet S) = true → False := by
            intro b' hb' hA
            simp only [Adm, decide_eq_true_eq] at hA
            exact Bool.noConfusion (hb' ▸ hA x hx)
          cases b
          case number => rfl
          case string => exact absurd h (fun hA => (hnone .string rfl hA).elim)
          case binary => exact absurd h (fun hA => (hnone .binary rfl hA).elim)
      | binSet S => obtain ⟨x, hx⟩ := S.2; cases b <;>
          simp_all [Adm, SetBase.adm, inD, occV, occOnly, Value.slot, SetBase.slot]
      | _ => exact absurd h (by simp [Adm])
  -- the containers write their own slot, whatever their elements read
  | .list _ _ _, _, v, h => Or.inl (by cases v <;> simp_all [denote, listCodec, occV, occOnly, Value.slot])
  | .object (.mk _ _ _), _, v, h => by
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp h
      obtain ⟨keys, f, g, rfl, -⟩ := objectCodecCore_e_inv ha
      exact Or.inl rfl
  | .held t P f g, ρ, v, h => by
      have hP : ((denote P ρ).e v).isSome = true := by
        simp only [denote, restrict_e_isSome, Bool.and_eq_true] at h; exact h.1
      rcases occV_open P ρ v hP with h1 | ⟨i, hi, he⟩
      · exact Or.inl (by simpa [occV] using h1)
      · exact Or.inr ⟨i, by simp only [Term.use, useHeld]; split <;> omega, he⟩
  | .refine t p, ρ, v, h => by
      have ht : ((denote t ρ).e v).isSome = true := by
        simp only [denote, restrict_e_isSome, Bool.and_eq_true] at h; exact h.2
      rcases occV_open t ρ v ht with h1 | ⟨i, hi, he⟩
      · exact Or.inl (by simpa [occV] using h1)
      · exact Or.inr ⟨i, by simpa [Term.use] using hi, he⟩
  | .union opts, ρ, v, h => by
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp h
      obtain ⟨o, ho, hoe, -⟩ := altCodec_e_admits ha
      rcases occV_openL opts ρ v o ho hoe with h1 | ⟨i, hi, he⟩
      · exact Or.inl (by simpa [occV] using h1)
      · exact Or.inr ⟨i, by simpa [Term.use] using hi, he⟩
  | .var j, _, _, h => Or.inr ⟨j, by simp [Term.use], h⟩
  -- a stage writes through the body at the stage before, and the first stage writes nothing
  | .mu b, ρ, v, h => by
      have hs : ∀ n, ((muStage (fun c => denote b (c :: ρ)) n).e v).isSome = true →
          occV b v.slot = true ∨ ∃ i, 2 ≤ b.use (i + 1) ∧ ((envAt ρ i).e v).isSome = true := by
        intro n
        induction n with
        | zero => intro h0; simp [muStage, Codec.empty] at h0
        | succ n ih =>
          intro hn
          rcases occV_open b _ v hn with h1 | ⟨i, hi, he⟩
          · exact Or.inl h1
          · match i, hi, he with
            | 0, _, he => exact ih he
            | i + 1, hi, he => exact Or.inr ⟨i, hi, he⟩
      rcases hs _ h with h1 | ⟨i, hi, he⟩
      · exact Or.inl (by simpa [occV] using h1)
      · exact Or.inr ⟨i, by simpa [Term.use] using hi, he⟩

/-- The options' companion: an option that writes a value writes it in the union's occupancy, or
    through a variable that reads the input. -/
theorem occV_openL : ∀ (ts : List Term) (ρ : List Codec) (v : Value) (o : Codec),
    o ∈ denoteList ts ρ → (o.e v).isSome = true →
      occVL ts v.slot = true ∨ ∃ i, 2 ≤ Term.useL i ts ∧ ((envAt ρ i).e v).isSome = true
  | [], _, _, _, ho, _ => nomatch ho
  | t :: ts, ρ, v, o, ho, h => by
      simp only [denoteList, List.mem_cons] at ho
      rcases ho with rfl | ho
      · rcases occV_open t ρ v h with h1 | ⟨i, hi, he⟩
        · exact Or.inl (occVL_cons (.inl h1))
        · exact Or.inr ⟨i, by simp only [Term.useL]; omega, he⟩
      · rcases occV_openL ts ρ v o ho h with h1 | ⟨i, hi, he⟩
        · exact Or.inl (occVL_cons (.inr h1))
        · exact Or.inr ⟨i, by simp only [Term.useL]; omega, he⟩

end

/-- **The write occupancy contains the row.** A closed term's variables are the bottom, so no
    variable writes, and the open lemma lands in the occupancy. -/
theorem occV_sound (t : Term) : OccSoundV t := fun v h =>
  (occV_open t [] v ((Adm_exact t v).mp h)).resolve_right
    fun ⟨_, _, he⟩ => by simp [envAt, Codec.empty] at he

def OccSoundA (t : Term) : Prop := ∀ a, AdmA t a = true → occA t a.member = true

/-- A read occupancy of an option is inside the read occupancy of the union. -/
theorem occAL_cons {t : Term} {ts : List Term} {m : Member}
    (h : occA t m = true ∨ occAL ts m = true) : occAL (t :: ts) m = true := by
  rcases h with h | h <;> simp [occAL, h]

mutual

/-- **The read occupancy contains what an open term reads**, or a variable that reads the term's
    own input reads it. The mirror of `occV_open`. -/
theorem occA_open : ∀ (t : Term) (ρ : List Codec) (a : Attr),
    ((denote t ρ).p a).isSome = true →
      occA t a.member = true ∨ ∃ i, 2 ≤ t.use i ∧ ((envAt ρ i).p a).isSome = true
  | .string, _, a, h | .number, _, a, h | .boolean, _, a, h | .binary, _, a, h
  | .null, _, a, h => Or.inl (by
      cases a <;> simp_all [denote, stringCodec, booleanCodec, binaryCodec, nullCodec,
        numberCodec, occA, occOnly, Attr.member])
  | .never, _, _, h => by simp [denote, Codec.empty] at h
  | .opaq, _, _, _ => Or.inl rfl
  | .literal k x, _, a, h => by
      have h := (AdmA_exact (.literal k x) a).mpr h
      rw [AdmA_literal] at h
      exact Or.inl (by
        cases k <;> cases a <;> simp_all [AdmALit, occA, occOnly, Attr.member, GroundKind.member])
  | .set b, _, a, h => by
      have h := (AdmA_exact (.set b) a).mpr h
      exact Or.inl (by
        cases b <;> cases a <;>
          simp_all [AdmA, AdmASet, occA, occOnly, Attr.member, SetBase.member])
  | .list _ _ _, _, a, h => Or.inl (by
      cases a <;> simp_all [denote, listCodec, occA, occOnly, Attr.member])
  | .object (.mk _ _ _), _, a, h => Or.inl (by
      cases a <;> simp_all [denote, bodySem, objectCodec, objectCodecCore, carriedCodec, mA,
        occA, occOnly, Attr.member])
  | .held t P f g, ρ, a, h => by
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h
      obtain ⟨hc, -⟩ := restrict_p.mp hw
      obtain ⟨u, hu, -⟩ := through_p.mp hc
      rcases occA_open t ρ a (by rw [hu]; rfl) with h1 | ⟨i, hi, he⟩
      · exact Or.inl (by simpa [occA] using h1)
      · exact Or.inr ⟨i, by simp only [Term.use, useHeld]; split <;> omega, he⟩
  | .refine t p, ρ, a, h => by
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h
      obtain ⟨hc, -⟩ := restrict_p.mp hw
      rcases occA_open t ρ a (by rw [hc]; rfl) with h1 | ⟨i, hi, he⟩
      · exact Or.inl (by simpa [occA] using h1)
      · exact Or.inr ⟨i, by simpa [Term.use] using hi, he⟩
  | .union opts, ρ, a, h => by
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h
      obtain ⟨o, ho, hop, -⟩ := altCodec_p_admits hw
      rcases occA_openL opts ρ a o ho hop with h1 | ⟨i, hi, he⟩
      · exact Or.inl (by simpa [occA] using h1)
      · exact Or.inr ⟨i, by simpa [Term.use] using hi, he⟩
  | .var j, _, _, h => Or.inr ⟨j, by simp [Term.use], h⟩
  | .mu b, ρ, a, h => by
      have hs : ∀ n, ((muStage (fun c => denote b (c :: ρ)) n).p a).isSome = true →
          occA b a.member = true ∨ ∃ i, 2 ≤ b.use (i + 1) ∧ ((envAt ρ i).p a).isSome = true := by
        intro n
        induction n with
        | zero => intro h0; simp [muStage, Codec.empty] at h0
        | succ n ih =>
          intro hn
          rcases occA_open b _ a hn with h1 | ⟨i, hi, he⟩
          · exact Or.inl h1
          · match i, hi, he with
            | 0, _, he => exact ih he
            | i + 1, hi, he => exact Or.inr ⟨i, hi, he⟩
      rcases hs _ h with h1 | ⟨i, hi, he⟩
      · exact Or.inl (by simpa [occA] using h1)
      · exact Or.inr ⟨i, by simpa [Term.use] using hi, he⟩

/-- The options' companion on the read side. -/
theorem occA_openL : ∀ (ts : List Term) (ρ : List Codec) (a : Attr) (o : Codec),
    o ∈ denoteList ts ρ → (o.p a).isSome = true →
      occAL ts a.member = true ∨ ∃ i, 2 ≤ Term.useL i ts ∧ ((envAt ρ i).p a).isSome = true
  | [], _, _, _, ho, _ => nomatch ho
  | t :: ts, ρ, a, o, ho, h => by
      simp only [denoteList, List.mem_cons] at ho
      rcases ho with rfl | ho
      · rcases occA_open t ρ a h with h1 | ⟨i, hi, he⟩
        · exact Or.inl (occAL_cons (.inl h1))
        · exact Or.inr ⟨i, by simp only [Term.useL]; omega, he⟩
      · rcases occA_openL ts ρ a o ho h with h1 | ⟨i, hi, he⟩
        · exact Or.inl (occAL_cons (.inr h1))
        · exact Or.inr ⟨i, by simp only [Term.useL]; omega, he⟩

end

/-- **The read occupancy contains the row.** The mirror of `occV_sound`. -/
theorem occA_sound (t : Term) : OccSoundA t := fun a h =>
  (occA_open t [] a ((AdmA_exact t a).mp h)).resolve_right
    fun ⟨_, _, he⟩ => by simp [envAt, Codec.empty] at he

/-! ## Separation

The families each option is confined to are the occupancy **intersected with the option's own
admission**. Disjointness in either factor makes the intersection disjoint, so the slot test
separates through the occupancy and the meet through the admission, with no second family. -/

def OrthSV (t : Term) : Value → Prop :=
  fun v => occV t v.slot = true ∧ Adm t v = true

def OrthSA (t : Term) : Attr → Prop :=
  fun a => occA t a.member = true ∧ AdmA t a = true

theorem occV_disjoint_of_Orth1 {x y : Term} (h : Orth1 x y = true) {s : Slot}
    (hx : occV x s = true) (hy : occV y s = true) : False := by
  have := List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).1 s (Slot.mem_all s)
  simp_all

theorem occA_disjoint_of_Orth1 {x y : Term} (h : Orth1 x y = true) {m : Member}
    (hx : occA x m = true) (hy : occA y m = true) : False := by
  have := List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2 m (Member.mem_all m)
  simp_all

/-- **What the discharger consumes.** Both families disjoint, as a `Prop`, of which the
    certificate is the decidable part. A new certificate is a new theorem producing `Separates`,
    not a new case in `pairwiseCompat_of_separated`. -/
def Separates (x y : Term) : Prop :=
  (∀ v, OrthSV x v → ¬ OrthSV y v) ∧ (∀ a, OrthSA x a → ¬ OrthSA y a)

/-- **The whole premise the discharger takes**, as one name: every pair of options separated.

    `Separates` is the rule for a pair and this is the rule for a list, so the certificate
    produces the first and a caller supplies the second.

    **It names the guarantee where the guarantee already lives, and moves nothing.** `Typed.union`
    cannot take it: `Separates` is stated on `Adm`, in `ExactV.lean`, and
    the import chain is `Typing` then `Soundness` then `Discharge` then `ExactA` then this
    file. A premise here is four modules above the judgement it would constrain. So an undischarged
    union stays *underivable* through `Obligations`, which is where it was, rather than becoming
    unrepresentable.

    **And unrepresentable is not available anyway.** A `Term.union` carrying its own witness needs
    either an inductive indexed by the option list it constrains, which is induction-induction, or
    a field whose type is computed from the term, which is induction-recursion. Lean 4 rejects both:
    the first as `unknown identifier` on the type being defined, the second as `invalid mutual
    block: either all elements of the block must be inductive/structure declarations, or they must
    all be definitions`. The one shape that works is a pre-term with a well-formedness subtype, and
    that re-founds the term language. -/
def Separated (opts : List Term) : Prop := List.Pairwise Separates opts

/-- **Pairwise separation bounds the admitters at one.** Separation says no two options admit
    one input, and admission implies occupancy through `occV_sound`, so the two conjuncts of
    `OrthSV` are both in hand. -/
theorem admitsAtMostOne_of_separated {opts : List Term} (h : Separated opts) :
    AdmitsAtMostOne (denoteList opts) := by
  constructor
  · intro v
    rw [filter_AdmList (fun t _ => Adm_exact t) v, List.length_map]
    refine length_le_one_of_pairwise_false (List.Pairwise.imp_of_mem ?_
      (List.Pairwise.filter _ (h.imp fun hs => hs.1 v)))
    intro x y hx hy hxy
    have hax : Adm x v = true := (List.mem_filter.mp hx).2
    have hay : Adm y v = true := (List.mem_filter.mp hy).2
    exact hxy ⟨occV_sound x v hax, hax⟩
      ⟨occV_sound y v hay, hay⟩
  · intro a
    rw [filter_AdmAList (fun t _ => AdmA_exact t) a, List.length_map]
    refine length_le_one_of_pairwise_false (List.Pairwise.imp_of_mem ?_
      (List.Pairwise.filter _ (h.imp fun hs => hs.2 a)))
    intro x y hx hy hxy
    have hax : AdmA x a = true := (List.mem_filter.mp hx).2
    have hay : AdmA y a = true := (List.mem_filter.mp hy).2
    exact hxy ⟨occA_sound x a hax, hax⟩
      ⟨occA_sound y a hay, hay⟩

/-- Two members that both meet `P`, in a list where no related pair both meets `P`, are one. -/
theorem eq_of_pairwise_excl {α : Type} {P : α → Prop} {R : α → α → Prop}
    (hR : ∀ x y, R x y → P x → P y → False) :
    ∀ {l : List α}, l.Pairwise R → ∀ x ∈ l, ∀ y ∈ l, P x → P y → x = y
  | [], _, _, hx, _, _, _, _ => nomatch hx
  | h :: tl, hp, x, hx, y, hy, px, py => by
    have hp' := List.pairwise_cons.mp hp
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · rfl
    · exact (hR _ _ (hp'.1 y hy') px py).elim
    · exact (hR _ _ (hp'.1 x hx') py px).elim
    · exact eq_of_pairwise_excl hR hp'.2 x hx' y hy' px py

/-- **Pairwise separation gives the union's obligation.** No input reaches two separated
    options, so an option never acts where another reads. -/
theorem pairwiseCompat_of_separated {opts : List Term}
    (hlaw : ∀ t ∈ opts, Lawful (denote t)) (h : Separated opts) : PairwiseCompat opts := by
  intro s hs t ht a v hp hact
  have hsA : AdmA s a = true := (AdmA_exact s a).mpr (by rw [hp]; rfl)
  have hsV : Adm s v = true := (Adm_exact s v).mpr ((hlaw s hs).defined hp)
  have hst : t = s := by
    rcases hact with hq | he
    · have htA : AdmA t a = true := (AdmA_exact t a).mpr hq
      exact eq_of_pairwise_excl (P := fun u => OrthSA u a) (fun x y hxy px py => hxy.2 a px py)
        h t ht s hs ⟨occA_sound t a htA, htA⟩
        ⟨occA_sound s a hsA, hsA⟩
    · have htV : Adm t v = true := (Adm_exact t v).mpr he
      exact eq_of_pairwise_excl (P := fun u => OrthSV u v) (fun x y hxy px py => hxy.1 v px py)
        h t ht s hs ⟨occV_sound t v htV, htV⟩
        ⟨occV_sound s v hsV, hsV⟩
  subst hst; exact hp

/-- Each codec is compatible with itself. -/
theorem compat_self (c : Codec) : Compat c c := fun _ _ hp _ => hp

/-- **An empty option is compatible with every option**: `never` reads nothing and writes
    nothing, so neither side of `Compat` has a case. -/
theorem compat_never_left (c : Codec) : Compat (denote .never) c := fun _ _ hp _ => nomatch hp

/-- …and on the other side. -/
theorem compat_never_right (c : Codec) : Compat c (denote .never) := fun _ _ _ hact => by
  rcases hact with h | h <;> exact nomatch h

/-- **A union with an empty option meets its obligation**, whatever the other option is. -/
theorem pairwiseCompat_never_right (x : Term) : PairwiseCompat [x, .never] := by
  intro s hs t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs ht
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
    first | exact compat_self _ | exact compat_never_left _ | exact compat_never_right _

/-- …and with the empty option first. -/
theorem pairwiseCompat_never_left (x : Term) : PairwiseCompat [.never, x] := by
  intro s hs t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs ht
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
    first | exact compat_self _ | exact compat_never_left _ | exact compat_never_right _

end Calculus
