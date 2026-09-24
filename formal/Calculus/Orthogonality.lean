import Calculus.ExactA

/-!
# Orthogonality — occupancy and separation

`Obligations (.union opts)` carries pairwise compatibility. Two separated options are compatible
(`pairwiseCompat_of_separated`). The decidable certificate is the meet (`certPair`, `Meet.lean`):
two options are orthogonal when their meet is the bottom, or when the meets of their two views are.
This module holds what the meet reads and what the certificate proves: the occupancies, the slot
test `Orth1` that the meet uses at the bottom, and `Separates`.

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
  | .lazy t      => occV t
  | .union opts  => occVL opts
  | .opaq  => occTop

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
  | .lazy t      => occA t
  | .union opts  => occAL opts
  | .opaq  => occTop

def occAL : List Term → Member → Bool
  | [] => fun _ => false
  | t :: ts => fun m => occA t m || occAL ts m
end

/-! ## The slot test -/

/-- **The slot test**: the write occupancies disjoint, and the read occupancies disjoint. The
    meet answers the bottom where it holds.

    **Two questions, and they coincide below `opaque`.** A `held` has its two occupancies in
    two coordinates: the write side is the caller-side term's, and the read side is the
    stored-side term's. A held-free term has one coordinate, and there the read occupancy
    lies inside the write occupancy (`occA_le_occV`, under `HF`). -/
def Orth1 (x y : Term) : Bool :=
  Slot.all.all (fun s => !(occV x s && occV y s)) &&
    Member.all.all (fun m => !(occA x m && occA y m))

/-! ## Soundness

Two structural recursions, one per side, each mutual with a list companion for `union`. The
statement is about the **rows** (`Adm`/`AdmA`) and about `admitOptV`/`admitOptA`, never about
the term's own rows: `select` filters by the *option* semantics, and for an object option that is
structure — the names and the literal fields, not every field's contents — so a certificate
stated on `Adm` alone would not transfer.
See `admitOptV`. -/

/-- `selOptV`'s disjunction, as an option it lands on. `AdmAny` is not enough here: at an
    *object* option the admission is `keysOk` and not `Adm`, so the union case has to hand its
    induction hypothesis the option's own test. -/
theorem selOptV_mem_admitOpt {opts : List Term} {v : Value}
    (h : selOptV (AdmSpecs opts) v = true) :
    ∃ t ∈ opts, admitOptV (specOf t, Adm t) v = true := by
  simp only [selOptV, AdmSpecs_eq, List.any_eq_true, List.mem_map] at h
  obtain ⟨_, ⟨t, ht, rfl⟩, hadm⟩ := h
  exact ⟨t, ht, hadm⟩

theorem selOptA_mem_admitOpt {opts : List Term} {a : Attr}
    (h : selOptA (AdmASpecs opts) a = true) :
    ∃ t ∈ opts, admitOptA (specOf t, AdmA t) a = true := by
  simp only [selOptA, AdmASpecs_eq, List.any_eq_true, List.mem_map] at h
  obtain ⟨_, ⟨t, ht, rfl⟩, hadm⟩ := h
  exact ⟨t, ht, hadm⟩

def OccSoundV (t : Term) : Prop := ∀ v, Adm t v = true → occV t v.slot = true

def OccSoundVL : List Term → Prop
  | [] => True
  | t :: ts => OccSoundV t ∧ OccSoundVL ts

theorem occSoundVL_mem : ∀ (ts : List Term), OccSoundVL ts → ∀ t ∈ ts, OccSoundV t
  | [], _, t, ht => absurd ht (by simp)
  | _ :: ts, h, t, ht => by
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact h.1
      · exact occSoundVL_mem ts h.2 t ht'

theorem occVL_of_mem {t : Term} {ts : List Term} {s : Slot} (ht : t ∈ ts)
    (h : occV t s = true) : occVL ts s = true := by
  induction ts with
  | nil => exact absurd ht (by simp)
  | cons _ ts ih =>
    rcases List.mem_cons.mp ht with rfl | h'
    · simp [occVL, h]
    · simp [occVL, ih h']

/-- Row soundness lifts to option soundness. At an object the row is not consulted at all:
    `keysOk` already says the value is a map, which is the only slot the term occupies. -/
theorem occV_admitOpt {t : Term} (h : OccSoundV t) (v : Value)
    (hv : admitOptV (specOf t, Adm t) v = true) : occV t v.slot = true :=
  h v hv

mutual

/-- **The write occupancy contains the row.** Twenty-one cases, and three are worth
    reading.

    `set b` is where nonemptiness of `℘⁺fin` does the work: the row matches all three wire
    families and asks `b.adm` element by element, so `set number` faced a `strSet` answers
    `∀ s ∈ S, inD (.str s)` — and `S` has an element, whose answer is `false`. Without
    nonemptiness a `set number` would admit the empty `strSet` and the sharp partition would
    be unsound.

    `literal k ls` is uniform in the base through `inL`, whose constructor pairing is exactly
    `GroundKind.slot`. -/
theorem occV_sound : ∀ (t : Term), OccSoundV t
  -- The rows whose `Adm` is a kind test and nothing more: one group, because a per-row
  -- proof here would be seven copies of one simp set. `number` is separate only because its
  -- gate `inD` has to be in the set.
  | .string | .boolean | .binary | .null =>
      fun v h => by cases v <;> simp_all [Adm, occV, occOnly, Value.slot]
  | .number => fun v h => by cases v <;> simp_all [Adm, inD, occV, occOnly, Value.slot]
  -- the row is `false`, so the premise is the one that cannot arrive
  | .never => fun _ h => by simp [Adm] at h

  | .literal k _ => fun v h => by
      rw [Adm_literal] at h
      cases k <;> cases v <;>
        simp_all [AdmLit, inL, occV, occOnly, Value.slot, GroundKind.slot]
  | .set b => fun v h => by
      cases v with
      | strSet S => obtain ⟨x, hx⟩ := S.2; cases b <;>
          simp_all [Adm, SetBase.adm, inD, occV, occOnly, Value.slot, SetBase.slot]
      -- the two bases that do not occupy `numSet` are refuted from the carrier's nonemptiness
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
  -- the containers, whose slot is fixed by the constructor and not by the payload
  | .list _ _ _ =>
      fun v h => by cases v <;> simp_all [Adm, occV, occOnly, Value.slot]
  | .object (.mk _ _ _) => fun v h => by
      cases v <;> simp_all [Adm, AdmBody, occV, occOnly, Value.slot]
  | .held _ P _ _ => fun v h => by
      simpa [occV] using occV_sound P v (Bool.and_eq_true_iff.mp h).2
  | .refine t _ => fun v h => by
      simpa [occV] using occV_sound t v (Bool.and_eq_true_iff.mp h).1
  | .lazy t => fun v h => by simpa [occV] using occV_sound t v h
  | .union opts => fun v h => by
      obtain ⟨t, ht, hadm⟩ := selOptV_mem_admitOpt (by rw [Adm_union] at h; exact h)
      exact occVL_of_mem ht
        (occV_admitOpt (occSoundVL_mem opts (occV_soundL opts) t ht) v hadm)
  | .opaq => fun _ _ => rfl

theorem occV_soundL : ∀ (ts : List Term), OccSoundVL ts
  | [] => trivial
  | t :: ts => ⟨occV_sound t, occV_soundL ts⟩
end

def OccSoundA (t : Term) : Prop := ∀ a, AdmA t a = true → occA t a.member = true

def OccSoundAL : List Term → Prop
  | [] => True
  | t :: ts => OccSoundA t ∧ OccSoundAL ts

theorem occSoundAL_mem : ∀ (ts : List Term), OccSoundAL ts → ∀ t ∈ ts, OccSoundA t
  | [], _, t, ht => absurd ht (by simp)
  | _ :: ts, h, t, ht => by
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact h.1
      · exact occSoundAL_mem ts h.2 t ht'

theorem occAL_of_mem {t : Term} {ts : List Term} {m : Member} (ht : t ∈ ts)
    (h : occA t m = true) : occAL ts m = true := by
  induction ts with
  | nil => exact absurd ht (by simp)
  | cons _ ts ih =>
    rcases List.mem_cons.mp ht with rfl | h'
    · simp [occAL, h]
    · simp [occAL, ih h']

theorem occA_admitOpt {t : Term} (h : OccSoundA t) (a : Attr)
    (ha : admitOptA (specOf t, AdmA t) a = true) : occA t a.member = true :=
  h a ha

mutual

/-- **The read occupancy contains the row.** The mirror of `occV_sound`. -/
theorem occA_sound : ∀ (t : Term), OccSoundA t
  -- One group where the write side needs three: on the read side the gates are gone, the
  -- stored member being what `Attr.member` already computes.
  | .string | .number | .boolean | .binary | .null =>
      fun a h => by cases a <;> simp_all [AdmA, occA, occOnly, Attr.member]
  | .never => fun _ h => by simp [AdmA] at h
  | .literal k _ => fun a h => by
      rw [AdmA_literal] at h
      cases k <;> cases a <;> simp_all [AdmALit, occA, occOnly, Attr.member, GroundKind.member]
  | .set b => fun a h => by
      cases b <;> cases a <;>
        simp_all [AdmA, AdmASet, occA, occOnly, Attr.member, SetBase.member]
  | .list _ _ _ =>
      fun a h => by cases a <;> simp_all [AdmA, occA, occOnly, Attr.member]
  | .object (.mk _ _ _) => fun a h => by
      cases a <;> simp_all [AdmA, AdmABody, occA, occOnly, Attr.member]
  | .refine t _ => fun a h => by
      simpa [occA] using occA_sound t a (Bool.and_eq_true_iff.mp h).1
  | .held t _ _ _ => fun a h => by
      simpa [occA] using occA_sound t a (Bool.and_eq_true_iff.mp h).1
  | .lazy t => fun a h => by simpa [occA] using occA_sound t a h
  | .union opts => fun a h => by
      obtain ⟨t, ht, hadm⟩ := selOptA_mem_admitOpt (by rw [AdmA_union] at h; exact h)
      exact occAL_of_mem ht
        (occA_admitOpt (occSoundAL_mem opts (occA_soundL opts) t ht) a hadm)
  | .opaq => fun _ _ => rfl

theorem occA_soundL : ∀ (ts : List Term), OccSoundAL ts
  | [] => trivial
  | t :: ts => ⟨occA_sound t, occA_soundL ts⟩
end

/-! ## Separation

The families each option is confined to are the occupancy **intersected with the option's own
admission**. Disjointness in either factor makes the intersection disjoint, so the slot test
separates through the occupancy and the meet through the admission, with no second family. -/

def OrthSV (t : Term) : Value → Prop :=
  fun v => occV t v.slot = true ∧ admitOptV (specOf t, Adm t) v = true

def OrthSA (t : Term) : Attr → Prop :=
  fun a => occA t a.member = true ∧ admitOptA (specOf t, AdmA t) a = true

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
    cannot take it: `Separates` is stated on `Adm` and `admitOptV`, both in `ExactV.lean`, and
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
    rw [filter_AdmSpecs (fun t _ => Adm_exact t) v, List.length_map]
    refine length_le_one_of_pairwise_false (List.Pairwise.imp_of_mem ?_
      (List.Pairwise.filter _ (h.imp fun hs => hs.1 v)))
    intro x y hx hy hxy
    have hax : admitOptV (specOf x, Adm x) v = true := (List.mem_filter.mp hx).2
    have hay : admitOptV (specOf y, Adm y) v = true := (List.mem_filter.mp hy).2
    exact hxy ⟨occV_admitOpt (occV_sound x) v hax, hax⟩
      ⟨occV_admitOpt (occV_sound y) v hay, hay⟩
  · intro a
    rw [filter_AdmASpecs (fun t _ => AdmA_exact t) a, List.length_map]
    refine length_le_one_of_pairwise_false (List.Pairwise.imp_of_mem ?_
      (List.Pairwise.filter _ (h.imp fun hs => hs.2 a)))
    intro x y hx hy hxy
    have hax : admitOptA (specOf x, AdmA x) a = true := (List.mem_filter.mp hx).2
    have hay : admitOptA (specOf y, AdmA y) a = true := (List.mem_filter.mp hy).2
    exact hxy ⟨occA_admitOpt (occA_sound x) a hax, hax⟩
      ⟨occA_admitOpt (occA_sound y) a hay, hay⟩

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
  have hsA : admitOptA (specOf s, AdmA s) a = true := (AdmA_exact s a).mpr (by rw [hp]; rfl)
  have hsV : admitOptV (specOf s, Adm s) v = true := (Adm_exact s v).mpr ((hlaw s hs).defined hp)
  have hst : t = s := by
    rcases hact with hq | he
    · have htA : admitOptA (specOf t, AdmA t) a = true := (AdmA_exact t a).mpr hq
      exact eq_of_pairwise_excl (P := fun u => OrthSA u a) (fun x y hxy px py => hxy.2 a px py)
        h t ht s hs ⟨occA_admitOpt (occA_sound t) a htA, htA⟩
        ⟨occA_admitOpt (occA_sound s) a hsA, hsA⟩
    · have htV : admitOptV (specOf t, Adm t) v = true := (Adm_exact t v).mpr he
      exact eq_of_pairwise_excl (P := fun u => OrthSV u v) (fun x y hxy px py => hxy.1 v px py)
        h t ht s hs ⟨occV_admitOpt (occV_sound t) v htV, htV⟩
        ⟨occV_admitOpt (occV_sound s) v hsV, hsV⟩
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
