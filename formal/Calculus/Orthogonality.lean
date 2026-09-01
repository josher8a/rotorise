import Calculus.Exactness

/-!
# Orthogonality — a decidable certificate for §5's (U)

`Typed.union` and `Obligations (.union opts)` between them carry two side conditions the
model has been discharging by hand, once per shape: `DIncomp` (§5's (D)) and `UAtAct` (§5's
residual (U)). Sixteen `sep*`/`uAtCan_*` theorems in `Discharge.lean`, `Exactness.lean` and
`Refutations.lean` do that work, and about thirteen of them are the *same rule* at different
constructors.

`Orth` is that rule, written once. It is a **phase classifier**: given a pair of terms it
answers whether there is a *syntactic certificate* that they cannot both admit one input.

## Sound, never complete, and why there is no `unknown`

Semantic orthogonality is undecidable in this language — `refine t q` carries an arbitrary
`Value → Bool`, `held t f g` an arbitrary pair of maps, `custom` an arbitrary pair of partial
functions. So `Orth` answers a *narrower* question, and the answer `false` means "no
certificate", never "not orthogonal".

The direction that keeps this sound is that **over-approximating an occupancy is always
safe**: if `X ⊆ X'`, `Y ⊆ Y'` and `X' ∩ Y' = ∅`, then `X ∩ Y = ∅`. So an opaque subterm
contributes `⊤` — every slot — and a pair involving it simply fails to be certified. There is
no third truth value to introduce.

## Both halves of the pair, independently

`uniqueAdmission_of_disjoint` takes **two** families, one over `Value` and one over `Attr`,
and asks each to be pairwise disjoint. That is not a redundancy to be optimized away: a pair
can be separated on one side and not on the other, and then it is not separated. Two
witnesses, in opposite directions, are why both families are carried here:

* `κ .number = some [.number]` and `κ .decimal = some [.string]` — a decimal's *value* is a
  `.str`, `GroundKind.decimal.toValue` says so — while `GroundKind.number.member` and
  `GroundKind.decimal.member` are both `.N`. So `union(number, decimal)` separates on the
  write side and not on the read side. `orth_number_decimal` is the check.
* `SetBase.string.slot` and `SetBase.decimal.slot` are both `.strSet` — a `set(decimal)`
  writes a set of *strings* — while `SetBase.string.member = .SS` and
  `SetBase.decimal.member = .NS`. So `union(set(string), set(decimal))` separates on the read
  side and not on the write side. `orth_set_string_decimal` is the check.

Neither pair is orthogonal, and each fails on a different half. `docs/codec-calculus.md:756`
states the asymmetry for the case that *does* separate — `union(set(string), set(number))`,
where "its options write different members, so reading was never in doubt".

## The write-side slot is the `Value` constructor, not `Kind`

`Kind` collapses `strSet`, `numSet` and `binSet` to `.set`, so `κ (set string)` and
`κ (set number)` are equal and the kind disjunct of `SepV` cannot separate them. The ten
`Value` constructors can, and `Adm (.set b)` is exact, so the sharper partition is *available
in the model*: the row for `set b` matches the payload's wire family and asks `b.adm` of its
elements, and `℘⁺fin` has no empty inhabitant, so a base admits exactly one family. `Slot`
below is that partition. (It is a statement about `Term`, not about any implementation: a
runtime `Set` that carries no element type has no such partition.)

The read-side slot is `Member`, which `Attr.member` already computes.

## The phases

| phase | separator | this module |
|---|---|---|
| slot | the `Value` constructor on the write side, the `Member` on the read side | `Orth1` |
| names | two-sided `keysOk` containment over the declared/required name sets | `OrthM` |
| tag | `tagOfV d`/`tagOfA d` | **not a phase of `Orth`** — see below |
| alternatives | two literals at one base with disjoint `ℓ` | not implemented |
| opaque predicate | `refine`'s `q`, `held`'s `f`, `custom` | undecidable by construction |

**The tag is not a phase of `Orth`, and this is a finding rather than an omission.** A
`union` option that is an object is admitted by `OptionSem.byNames` — `keysOk`, a test on the
*names* the map carries — so `select` never looks at any field's contents, discriminator
included. Two object options with disjoint `req`-literal discriminators on the same name are
therefore **not** separated at a `union`; they are separated at a `dunion`, whose options are
`OptionSem.byTag` and whose (U) is already the theorem `uAtCan_dunion`. So the tag row of
§5's table belongs to a different constructor, not to a phase here.
-/

namespace Calculus

/-! ## Slots

`Slot` is the `Value` constructor as data. `Member` is reused unchanged for the read side —
`Attr.member` is already the constructor tag there.

`Slot` is *not* `Member` with the names changed, and reusing `Member` for both sides would be
the bug this module exists to avoid: `decimal` writes a `.str` and stores an `N`, and
`set decimal` writes a `.strSet` and stores an `NS`, so the two tags disagree exactly where
the separation argument needs them to. -/

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
    `decide` over these is the whole of what makes `Orth` checkable by `by decide`. -/
def Slot.all : List Slot :=
  [.str, .num, .bool, .bin, .null, .strSet, .numSet, .binSet, .arr, .map]

theorem Slot.mem_all (s : Slot) : s ∈ Slot.all := by cases s <;> simp [Slot.all]

def Member.all : List Member := [.S, .N, .B, .BOOL, .NULL, .SS, .NS, .BS, .L, .M]

theorem Member.mem_all (m : Member) : m ∈ Member.all := by cases m <;> simp [Member.all]

/-- A literal base's *value* slot. Not `GroundKind.member`, and `decimal` is the whole
    reason: it holds its numeral as text, so its values are `.str` and its attributes are
    `N`. -/
def GroundKind.slot : GroundKind → Slot
  | .string  => .str
  | .number  => .num
  | .decimal => .str
  | .boolean => .bool
  | .binary  => .bin
  | .null    => .null

/-- A set base's value slot — the wire family its payload sits in. Four bases onto three
    slots, and the collision is `string`/`decimal`, where `SetBase.member` collides at
    `number`/`decimal` instead. The two collisions are disjoint, which is why the pair of
    families separates all four bases and neither family does alone. -/
def SetBase.slot : SetBase → Slot
  | .string  => .strSet
  | .number  => .numSet
  | .decimal => .strSet
  | .binary  => .binSet

/-! ## Occupancy

An occupancy is a total map from slot to `Bool` — the three-element lattice `∅ | only s | ⊤`
with no separate representation, since a `Slot → Bool` is already the powerset and the
lattice operations are `||` and `&&`.

Computed from **one** term, never from a pair. A pairwise case analysis would be `n²` over
twenty-one constructors; this is `n`, and the pair only ever compares two answers. -/

def occOnly {α : Type} [DecidableEq α] (x : α) : α → Bool := fun y => decide (y = x)
def occTop {α : Type} : α → Bool := fun _ => true
def occWith {α : Type} [DecidableEq α] (x : α) (o : α → Bool) : α → Bool :=
  fun y => decide (y = x) || o y
def occBut {α : Type} [DecidableEq α] (x : α) : α → Bool := fun y => !decide (y = x)

mutual

/-- **Which value constructors this term can write.** An over-approximation of
    `{v.slot | Adm t v}`, and `occV_sound` is that containment.

    The `⊤` rows, and why each is `⊤` rather than sharper — `docs/codec-calculus.md:786-806`
    tabulates the same four:

    * `held t f _` — `f` is an arbitrary `Value → Value` applied *before* the subterm's row,
      so it can move the value into any constructor. `⊤`. (The read side is not: `g`
      post-processes, so `AdmA (.held t f g) = AdmA t` and the read occupancy is the
      subterm's.)
    * `custom _ _` — arbitrary partial functions both ways. `⊤` on both sides.
    * `refine t q` — the subterm's, over-approximating away `q`. Sound: a refinement writes
      a subset of what the base writes.
    * `legacy t _` — the subterm's on the write side; `r` only widens the *read*.
    * `nullable t` — the subterm's plus `null`. Always adding `null` is the sound
      over-approximation; asking `(denote t).ownsNull` would be sharper and is a computable
      `Bool`, but the sharpening buys nothing a pair can use, since a term that owns null
      already occupies the slot.
    * `opaq lossy` — a closed form, because `opaque` is a fixed list of options: every slot,
      minus `num` when the numeric option is `Codec.empty`. This is itself an
      over-approximation in one place — `adm_opaq_false_numSet` shows a non-lossy `opaque`
      refuses a `numSet` too, since `opaqCodecω` budgets by the input's own depth and its
      element codec refuses numbers — and the sound direction is to keep `numSet`.
    * `union opts` — the union of the options'. `select` admits only where *exactly one*
      option does, so the union of the options' occupancies is an over-approximation. -/
def occV : Term → Slot → Bool
  | .string  => occOnly .str
  | .number  => occOnly .num
  | .decimal => occOnly .str
  | .boolean => occOnly .bool
  | .binary  => occOnly .bin
  | .null    => occOnly .null
  | .literal k _ => occOnly k.slot
  | .set b       => occOnly b.slot
  | .array _     => occOnly .arr
  | .tuple _ _   => occOnly .arr
  | .record _    => occOnly .map
  | .object _ _ _ => occOnly .map
  | .dunion _ _  => occOnly .map
  | .held _ _ _  => occTop
  | .custom _ _  => occTop
  | .refine t _  => occV t
  | .legacy t _  => occV t
  | .lazy t      => occV t
  | .nullable t  => occWith .null (occV t)
  | .union opts  => occVL opts
  | .opaq lossy  => if lossy then occTop else occBut .num

def occVL : List Term → Slot → Bool
  | [] => fun _ => false
  | t :: ts => fun s => occV t s || occVL ts s
end

mutual

/-- **Which members this term can read.** The mirror, and it is not a symmetric mirror:
    `held` and `legacy` swap sides.

    `legacy t r` is `⊤` here where it was the subterm's on the write side, and the reason is
    the *row*, not the codec: `AdmA (.legacy t r) a = AdmA t a || (r a).isSome`, and `r` is
    arbitrary data the term carries. A lawful `legacyCodec` does respect the member —
    `μSyn (.legacy t _) = μSyn t`, and `ReadsCoherently` is what makes that good — but
    `Orth` is stated on the row, which is looser, so the certificate declines. That is the
    one place where `μSyn` is sharper than `occA`, and it is sharper only under an
    obligation `Orth` does not take as a premise. -/
def occA : Term → Member → Bool
  | .string  => occOnly .S
  | .number  => occOnly .N
  | .decimal => occOnly .N
  | .boolean => occOnly .BOOL
  | .binary  => occOnly .B
  | .null    => occOnly .NULL
  | .literal k _ => occOnly k.member
  | .set b       => occOnly b.member
  | .array _     => occOnly .L
  | .tuple _ _   => occOnly .L
  | .record _    => occOnly .M
  | .object _ _ _ => occOnly .M
  | .dunion _ _  => occOnly .M
  | .legacy _ _  => occTop
  | .custom _ _  => occTop
  | .refine t _  => occA t
  | .held t _ _  => occA t
  | .lazy t      => occA t
  | .nullable t  => occWith .NULL (occA t)
  | .union opts  => occAL opts
  | .opaq lossy  => if lossy then occTop else occBut .N

def occAL : List Term → Member → Bool
  | [] => fun _ => false
  | t :: ts => fun m => occA t m || occAL ts m
end

/-! ## The classifier -/

/-- **Phase *slot*.** Both occupancies disjoint — and *both*, conjoined, because a pair
    separated on one side only is not separated. -/
def Orth1 (x y : Term) : Bool :=
  Slot.all.all (fun s => !(occV x s && occV y s)) &&
  Member.all.all (fun m => !(occA x m && occA y m))

/-- One option requires a name the other does not declare.

    This is the whole of the name test, and it is a consequence of `keysOk` being **two-sided
    containment** rather than disjointness of a label set: `keysOk spec keys` asks that every
    present name is declared *and* that every required name is present. So the key sets one
    spec admits are exactly the interval `[req spec, decl spec]`, and two intervals meet iff
    `req x ∪ req y ⊆ decl x ∩ decl y`. Since `req ⊆ decl` always, that fails exactly when one
    side requires a name the other does not declare. -/
def reqNotDeclared (sx sy : MapOf Bool) : Bool :=
  decide (∃ k : {k // k ∈ sx.1}, sx.2 k = true ∧ k.1 ∉ sy.1)

/-- **Phase *names*.** Two object options whose admissible key-set intervals are disjoint.

    In `src/` this is the second most common separator in practice — unions of objects with
    no shared attribute at all — and it is invisible to phases based on slots, since both
    options occupy `map` and `M` and nothing else.

    **An optional binding widens admission**, which is the ambiguity
    `docs/codec-calculus.md:711` names: two objects declaring only *optional* names both
    admit the empty map, so they are never separated here however disjoint their names.
    `orth_objects_optional_only` is that check, and it answers `false`. -/
def OrthM (x y : Term) : Bool :=
  match specOf x, specOf y with
  | some sx, some sy => reqNotDeclared sx sy || reqNotDeclared sy sx
  | _, _ => false

/-- **The classifier.** A syntactic, decidable certificate that two terms cannot both admit
    one input — on both halves of the pair. `false` means "no certificate found". -/
def Orth (x y : Term) : Bool := Orth1 x y || OrthM x y

/-! ## Soundness

Two structural recursions, one per side, each mutual with a list companion for `union`. The
statement is about the **rows** (`Adm`/`AdmA`) and about `admitOptV`/`admitOptA`, never about
`adm`/`admA`: `select` filters by the *option* semantics, and for an object option that is
`keysOk` — names, not contents — so a certificate stated on `Adm` alone would not transfer.
See `admitOptV`. -/

theorem specOf_none_admitOptV {t : Term} (h : specOf t = none) (v : Value) :
    admitOptV (specOf t, Adm t) v = Adm t v := by simp only [admitOptV, h]

theorem specOf_none_admitOptA {t : Term} (h : specOf t = none) (a : Attr) :
    admitOptA (specOf t, AdmA t) a = AdmA t a := by simp only [admitOptA, h]

/-- `selOptV`'s singleton, as the option it lands on — `selOptV_le_AdmAny` in the vocabulary
    the recursion needs. `AdmAny` is not enough here: at an *object* option the admission is
    `keysOk` and not `Adm`, so the union case has to hand its induction hypothesis the
    option's own test. -/
theorem selOptV_mem_admitOpt {opts : List Term} {v : Value}
    (h : selOptV (AdmSpecs opts) v = true) :
    ∃ t ∈ opts, admitOptV (specOf t, Adm t) v = true := by
  simp only [selOptV, AdmSpecs_eq] at h
  cases hf : (opts.map fun t => (specOf t, Adm t)).filter (fun o => admitOptV o v) with
  | nil => rw [hf] at h; exact absurd h (by simp)
  | cons o rest =>
    cases rest with
    | cons _ _ => rw [hf] at h; exact absurd h (by simp)
    | nil =>
      have hmemf : o ∈ (opts.map fun t => (specOf t, Adm t)).filter
          (fun o => admitOptV o v) := by rw [hf]; simp
      have hadm : admitOptV o v = true := (List.mem_filter.mp hmemf).2
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (List.mem_of_mem_filter hmemf)
      exact ⟨t, ht, hadm⟩

theorem selOptA_mem_admitOpt {opts : List Term} {a : Attr}
    (h : selOptA (AdmASpecs opts) a = true) :
    ∃ t ∈ opts, admitOptA (specOf t, AdmA t) a = true := by
  simp only [selOptA, AdmASpecs_eq] at h
  cases hf : (opts.map fun t => (specOf t, AdmA t)).filter (fun o => admitOptA o a) with
  | nil => rw [hf] at h; exact absurd h (by simp)
  | cons o rest =>
    cases rest with
    | cons _ _ => rw [hf] at h; exact absurd h (by simp)
    | nil =>
      have hmemf : o ∈ (opts.map fun t => (specOf t, AdmA t)).filter
          (fun o => admitOptA o a) := by rw [hf]; simp
      have hadm : admitOptA o a = true := (List.mem_filter.mp hmemf).2
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (List.mem_of_mem_filter hmemf)
      exact ⟨t, ht, hadm⟩

/-- Only an object has a name spec — the fact that lets the `admitOptV` wrapper below split
    into two cases instead of twenty-one. -/
theorem specOf_some_object {t : Term} {spec : MapOf Bool} (h : specOf t = some spec) :
    ∃ f ff r, t = .object f ff r := by
  cases t <;> simp_all [specOf]

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
    (hv : admitOptV (specOf t, Adm t) v = true) : occV t v.slot = true := by
  cases hs : specOf t with
  | none => exact h v (by rw [admitOptV, hs] at hv; exact hv)
  | some spec =>
      obtain ⟨f, ff, r, rfl⟩ := specOf_some_object hs
      cases v <;> simp_all [admitOptV, specOf, occV, occOnly, Value.slot]

/-- `Adm` and `adm` are the same function at `opaq` — both ask `opaqCodecω` — so the table's
    `opaque` lemmas apply to the joint row verbatim. -/
theorem Adm_opaq_eq_adm (lossy : Bool) (v : Value) :
    Adm (.opaq lossy) v = adm (.opaq lossy) v := rfl

theorem AdmA_opaq_eq_admA (lossy : Bool) (a : Attr) :
    AdmA (.opaq lossy) a = admA (.opaq lossy) a := rfl

mutual

/-- **The write occupancy contains the row.** Twenty-one cases, and three are worth
    reading.

    `set b` is where nonemptiness of `℘⁺fin` does the work: the row matches all three wire
    families and asks `b.adm` element by element, so `set number` faced a `strSet` answers
    `∀ s ∈ S, inD (.str s)` — and `S` has an element, whose answer is `false`. Without
    nonemptiness a `set number` would admit the empty `strSet` and the sharp partition would
    be unsound.

    `literal k ls` is uniform in the base through `inL`, whose constructor pairing is exactly
    `GroundKind.slot`; `decimal`'s `dif` on `Numeral.Stored` does not change which
    constructor it matches.

    `opaq false` is the one appeal to a `⊤`-row lemma from the table (`adm_opaq_false_num`),
    and it is available because the row asks the codec. -/
theorem occV_sound : ∀ (t : Term), OccSoundV t
  | .string => fun v h => by cases v <;> simp_all [Adm, occV, occOnly, Value.slot]
  | .number => fun v h => by cases v <;> simp_all [Adm, inD, occV, occOnly, Value.slot]
  | .decimal => fun v h => by cases v <;> simp_all [Adm, isStored, occV, occOnly, Value.slot]
  | .boolean => fun v h => by cases v <;> simp_all [Adm, occV, occOnly, Value.slot]
  | .binary => fun v h => by cases v <;> simp_all [Adm, occV, occOnly, Value.slot]
  | .null => fun v h => by cases v <;> simp_all [Adm, occV, occOnly, Value.slot]
  | .literal k _ => fun v h => by
      rw [Adm_literal] at h
      cases k <;> cases v <;>
        simp_all [AdmLit, inL, occV, occOnly, Value.slot, GroundKind.slot]
  | .set b => fun v h => by
      cases v with
      | strSet S => obtain ⟨x, hx⟩ := S.2; cases b <;>
          simp_all [Adm, SetBase.adm, inD, isStored, occV, occOnly, Value.slot, SetBase.slot]
      | numSet S => obtain ⟨x, hx⟩ := S.2; cases b <;>
          simp_all [Adm, SetBase.adm, inD, isStored, occV, occOnly, Value.slot, SetBase.slot]
      | binSet S => obtain ⟨x, hx⟩ := S.2; cases b <;>
          simp_all [Adm, SetBase.adm, inD, isStored, occV, occOnly, Value.slot, SetBase.slot]
      | _ => exact absurd h (by simp [Adm])
  | .array _ => fun v h => by cases v <;> simp_all [Adm, occV, occOnly, Value.slot]
  | .tuple _ _ => fun v h => by cases v <;> simp_all [Adm, occV, occOnly, Value.slot]
  | .record _ => fun v h => by cases v <;> simp_all [Adm, occV, occOnly, Value.slot]
  | .dunion _ _ => fun v h => by
      cases v <;> simp_all [Adm, selTagV, tagOfV, occV, occOnly, Value.slot]
  | .object _ _ _ => fun v h => by cases v <;> simp_all [Adm, occV, occOnly, Value.slot]
  | .held _ _ _ => fun _ _ => rfl
  | .custom _ _ => fun _ _ => rfl
  | .refine t _ => fun v h => by
      simpa [occV] using occV_sound t v (Bool.and_eq_true_iff.mp h).1
  | .legacy t _ => fun v h => by simpa [occV] using occV_sound t v h
  | .lazy t => fun v h => by simpa [occV] using occV_sound t v h
  | .nullable t => fun v h => by
      simp only [Adm, Bool.or_eq_true] at h
      rcases h with h | h
      · simp only [occV, occWith, Bool.or_eq_true]; exact Or.inr (occV_sound t v h)
      · cases v <;> simp_all [occV, occWith, Value.slot]
  | .union opts => fun v h => by
      obtain ⟨t, ht, hadm⟩ := selOptV_mem_admitOpt (by rw [Adm_union] at h; exact h)
      exact occVL_of_mem ht
        (occV_admitOpt (occSoundVL_mem opts (occV_soundL opts) t ht) v hadm)
  | .opaq lossy => fun v h => by
      cases lossy with
      | true => rfl
      | false =>
        cases v <;> simp only [occV, occBut, Value.slot, if_false, Bool.false_eq_true] <;>
          first
            | rfl
            | (exact absurd h (by simp [Adm_opaq_eq_adm, adm_opaq_false_num]))

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
    (ha : admitOptA (specOf t, AdmA t) a = true) : occA t a.member = true := by
  cases hs : specOf t with
  | none => exact h a (by rw [admitOptA, hs] at ha; exact ha)
  | some spec =>
      obtain ⟨f, ff, r, rfl⟩ := specOf_some_object hs
      cases a <;> simp_all [admitOptA, specOf, occA, occOnly, Attr.member]

/-- A decimal literal reads only an `N`, and the row cannot be read off syntactically because
    it *asks its codec* — `AdmALit .decimal ls a = ((literalCodec .decimal ls).p a).isSome`.
    So the member comes from (W) on the read side instead: `Lawful.reads` says a
    member-naming codec accepts no other member, and `literalCodec_μ` names it. -/
theorem admALit_decimal_member {ls : NEFinset GroundKind.decimal.Carrier} {a : Attr}
    (h : AdmALit .decimal ls a = true) : a.member = .N := by
  obtain ⟨v, hp⟩ := Option.isSome_iff_exists.mp (by simpa [AdmALit] using h)
  exact (lawful_literalCodec .decimal ls).reads (literalCodec_μ .decimal ls) hp

mutual

/-- **The read occupancy contains the row.** The mirror of `occV_sound`, with `held` and
    `legacy` on the other sides and `literal .decimal` going through (W) rather than through
    a pattern. -/
theorem occA_sound : ∀ (t : Term), OccSoundA t
  | .string => fun a h => by cases a <;> simp_all [AdmA, occA, occOnly, Attr.member]
  | .number => fun a h => by cases a <;> simp_all [AdmA, occA, occOnly, Attr.member]
  | .decimal => fun a h => by cases a <;> simp_all [AdmA, occA, occOnly, Attr.member]
  | .boolean => fun a h => by cases a <;> simp_all [AdmA, occA, occOnly, Attr.member]
  | .binary => fun a h => by cases a <;> simp_all [AdmA, occA, occOnly, Attr.member]
  | .null => fun a h => by cases a <;> simp_all [AdmA, occA, occOnly, Attr.member]
  | .literal k _ => fun a h => by
      rw [AdmA_literal] at h
      cases k with
      | decimal => simp [occA, occOnly, GroundKind.member, admALit_decimal_member h]
      | _ => cases a <;> simp_all [AdmALit, occA, occOnly, Attr.member, GroundKind.member]
  | .set b => fun a h => by
      cases b <;> cases a <;>
        simp_all [AdmA, AdmASet, occA, occOnly, Attr.member, SetBase.member]
  | .array _ => fun a h => by cases a <;> simp_all [AdmA, occA, occOnly, Attr.member]
  | .tuple _ _ => fun a h => by cases a <;> simp_all [AdmA, occA, occOnly, Attr.member]
  | .record _ => fun a h => by cases a <;> simp_all [AdmA, occA, occOnly, Attr.member]
  | .object _ _ _ => fun a h => by cases a <;> simp_all [AdmA, occA, occOnly, Attr.member]
  | .dunion _ _ => fun a h => by
      cases a <;> simp_all [AdmA, selTagA, tagOfA, occA, occOnly, Attr.member]
  | .legacy _ _ => fun _ _ => rfl
  | .custom _ _ => fun _ _ => rfl
  | .refine t _ => fun a h => by
      simpa [occA] using occA_sound t a (Bool.and_eq_true_iff.mp h).1
  | .held t _ _ => fun a h => by simpa [occA] using occA_sound t a h
  | .lazy t => fun a h => by simpa [occA] using occA_sound t a h
  | .nullable t => fun a h => by
      simp only [AdmA, Bool.or_eq_true] at h
      rcases h with h | h
      · simp only [occA, occWith, Bool.or_eq_true]; exact Or.inr (occA_sound t a h)
      · cases a <;> simp_all [occA, occWith, Attr.member]
  | .union opts => fun a h => by
      obtain ⟨t, ht, hadm⟩ := selOptA_mem_admitOpt (by rw [AdmA_union] at h; exact h)
      exact occAL_of_mem ht
        (occA_admitOpt (occSoundAL_mem opts (occA_soundL opts) t ht) a hadm)
  | .opaq lossy => fun a h => by
      cases lossy with
      | true => rfl
      | false =>
        cases a <;> simp only [occA, occBut, Attr.member, if_false, Bool.false_eq_true] <;>
          first
            | rfl
            | (exact absurd h (by simp [AdmA_opaq_eq_admA, admA_opaq_false_n]))

theorem occA_soundL : ∀ (ts : List Term), OccSoundAL ts
  | [] => trivial
  | t :: ts => ⟨occA_sound t, occA_soundL ts⟩
end

/-! ## Discharging (U)

The families each option is confined to are the occupancy **intersected with the option's own
admission**. That is the same move `SVof`/`SAof` make, and it is what lets one pair of
families serve every phase: disjointness in either factor makes the intersection disjoint, so
phase *slot* separates through the occupancy and phase *names* through the admission, with no
second family and no case analysis at the discharger. -/

def OrthSV (t : Term) : Value → Prop :=
  fun v => occV t v.slot = true ∧ admitOptV (specOf t, Adm t) v = true

def OrthSA (t : Term) : Attr → Prop :=
  fun a => occA t a.member = true ∧ admitOptA (specOf t, AdmA t) a = true

theorem occV_disjoint_of_Orth1 {x y : Term} (h : Orth1 x y = true) {s : Slot}
    (hx : occV x s = true) (hy : occV y s = true) : False := by
  have h1 := (Bool.and_eq_true_iff.mp h).1
  have := List.all_eq_true.mp h1 s (Slot.mem_all s)
  simp_all

theorem occA_disjoint_of_Orth1 {x y : Term} (h : Orth1 x y = true) {m : Member}
    (hx : occA x m = true) (hy : occA y m = true) : False := by
  have h1 := (Bool.and_eq_true_iff.mp h).2
  have := List.all_eq_true.mp h1 m (Member.mem_all m)
  simp_all

/-- The name test really is disjointness of the admitted key sets: the name one option
    requires is present in any map it admits, and absent from the other's declarations, so
    the other refuses that map on its first `keysOk` conjunct. -/
theorem keysOk_of_reqNotDeclared {sx sy : MapOf Bool} (h : reqNotDeclared sx sy = true)
    {keys : Finset Name} (hx : keysOk sx keys = true) (hy : keysOk sy keys = true) : False := by
  obtain ⟨k, hreq, hnd⟩ := of_decide_eq_true h
  have hpres : k.1 ∈ keys := (of_decide_eq_true (Bool.and_eq_true_iff.mp hx).2) k hreq
  exact hnd ((of_decide_eq_true (Bool.and_eq_true_iff.mp hy).1) k.1 hpres)

theorem orthM_spec {x y : Term} (h : OrthM x y = true) :
    ∃ sx sy, specOf x = some sx ∧ specOf y = some sy ∧
      (reqNotDeclared sx sy = true ∨ reqNotDeclared sy sx = true) := by
  unfold OrthM at h
  cases hsx : specOf x with
  | none => rw [hsx] at h; exact absurd h (by simp)
  | some sx =>
    cases hsy : specOf y with
    | none => rw [hsx, hsy] at h; exact absurd h (by simp)
    | some sy =>
      rw [hsx, hsy] at h
      exact ⟨sx, sy, rfl, rfl, Bool.or_eq_true_iff.mp h⟩

theorem orthSV_disjoint {x y : Term} (h : Orth x y = true) :
    ∀ v, OrthSV x v → ¬ OrthSV y v := by
  rintro v ⟨hox, hax⟩ ⟨hoy, hay⟩
  rcases Bool.or_eq_true_iff.mp h with h1 | hm
  · exact occV_disjoint_of_Orth1 h1 hox hoy
  · obtain ⟨sx, sy, hsx, hsy, hr⟩ := orthM_spec hm
    rw [hsx] at hax; rw [hsy] at hay
    cases v with
    | map keys g =>
      have hkx : keysOk sx keys = true := by simpa [admitOptV] using hax
      have hky : keysOk sy keys = true := by simpa [admitOptV] using hay
      rcases hr with hr | hr
      · exact keysOk_of_reqNotDeclared hr hkx hky
      · exact keysOk_of_reqNotDeclared hr hky hkx
    | _ => exact absurd hax (by simp [admitOptV])

theorem orthSA_disjoint {x y : Term} (h : Orth x y = true) :
    ∀ a, OrthSA x a → ¬ OrthSA y a := by
  rintro a ⟨hox, hax⟩ ⟨hoy, hay⟩
  rcases Bool.or_eq_true_iff.mp h with h1 | hm
  · exact occA_disjoint_of_Orth1 h1 hox hoy
  · obtain ⟨sx, sy, hsx, hsy, hr⟩ := orthM_spec hm
    rw [hsx] at hax; rw [hsy] at hay
    cases a with
    | m keys g =>
      have hkx : keysOk sx keys = true := by simpa [admitOptA] using hax
      have hky : keysOk sy keys = true := by simpa [admitOptA] using hay
      rcases hr with hr | hr
      · exact keysOk_of_reqNotDeclared hr hkx hky
      · exact keysOk_of_reqNotDeclared hr hky hkx
    | _ => exact absurd hax (by simp [admitOptA])

/-- **§5's (U), from one decidable premise.** Pairwise `Orth` over the options, and the two
    premises every discharger in `Discharge.lean` already takes: lawfulness, which soundness
    supplies, and the closed-object restriction.

    `hcl` is not a defect being worked around. An object option with an open rest
    (`.codec t`) has `Adm t v = true` where `admitOptV … v = false` — the option refuses maps
    its own `e` accepts — and `docs/codec-calculus.md:713` argues that this is the intended
    reading ("an open object that must be an option should declare what it means to keep").
    `optionSem_self_admit` takes the same premise for the same reason. `Orth` declines to
    certify such an option rather than proposing a repair.

    Thirteen of the sixteen hand `sep*`/`uAtCan_*` theorems are instances of this. What it
    does not reach is recorded below: phase *alternatives* (two literals at one base with
    disjoint `ℓ`) is not implemented, and phase *opaque predicate* cannot be. -/
theorem uAtCan_of_orth {opts : List Term}
    (hlaw : ∀ t ∈ opts, Lawful (denote t))
    (hcl : ∀ t ∈ opts, ∀ fields ff tr, t ≠ .object fields ff (.codec tr))
    (h : List.Pairwise (fun x y => Orth x y = true) opts) :
    UAtCan opts := by
  refine uniqueAdmission_of_disjoint
    (SVs := opts.map OrthSV) (SAs := opts.map OrthSA) ?_ ?_ ?_ ?_ ?_
  · rw [semsOf, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine List.forall₂_same.mpr fun t _ v hv => ?_
    rw [admitOptV_eq (Adm_exact t) v] at hv
    exact ⟨occV_admitOpt (occV_sound t) v hv, hv⟩
  · rw [semsOf, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine List.forall₂_same.mpr fun t _ a ha => ?_
    rw [admitOptA_eq (AdmA_exact t) a] at ha
    exact ⟨occA_admitOpt (occA_sound t) a ha, ha⟩
  · rw [List.pairwise_map]; exact h.imp orthSV_disjoint
  · rw [List.pairwise_map]; exact h.imp orthSA_disjoint
  · refine forall_mem_map fun t ht v a he => ?_
    rw [optionSemOf_c] at he
    exact optionSem_self_admit t (hcl t ht) (hlaw t ht) he

/-- …and the residue the laws actually need. -/
theorem uAtAct_of_orth {opts : List Term}
    (hlaw : ∀ t ∈ opts, Lawful (denote t))
    (hcl : ∀ t ∈ opts, ∀ fields ff tr, t ≠ .object fields ff (.codec tr))
    (h : List.Pairwise (fun x y => Orth x y = true) opts) :
    UAtAct opts :=
  uAtAct_of_uAtCan (uAtCan_of_orth hlaw hcl h)

/-! ## The classifier, checked against the table

`Orth` is decidable, so the checks below are `by decide` rather than proofs — which is the
point of having it. The negatives matter more than the positives: **the ten `not_sep*`
witnesses are a ready-made unsoundness test suite**, and if `Orth` certified one of them
`Orth` would be wrong. It certifies none. -/

private def lsA : NEFinset String := ⟨{"A"}, Finset.singleton_nonempty _⟩
private def lsB : NEFinset String := ⟨{"B"}, Finset.singleton_nonempty _⟩

theorem orth_string_number : Orth .string .number = true := by decide
theorem orth_string_null : Orth .string .null = true := by decide
theorem orth_string_boolean : Orth .string .boolean = true := by decide
theorem orth_string_dunion : Orth .string (.dunion "k" []) = true := by decide
theorem orth_array_record : Orth (.array .string) (.record .string) = true := by decide

/-- §5's worked `(set)` example, and out of reach of `SepV`'s kind disjunct: `κ` collapses
    both options to `.set`. The `Value` constructor does not. -/
theorem orth_set_string_number : Orth (.set .string) (.set .number) = true := by decide

/-- `opaque` with `numbers = 'refuse'` writes no number and reads no `N`, and the certificate
    sees it because the occupancy is a closed form rather than a `⊤`. -/
theorem orth_number_opaque : Orth .number (.opaq false) = true := by decide

/-- **Separated on the write side only, hence not separated.** A decimal's value is a `.str`
    and a number's is a `.num`; both store `N`. -/
theorem orth_number_decimal : Orth .number .decimal = false := by decide

/-- **Separated on the read side only, hence not separated.** `set(decimal)` writes a
    `.strSet` exactly as `set(string)` does; they store `NS` and `SS`. -/
theorem orth_set_string_decimal : Orth (.set .string) (.set .decimal) = false := by decide

/-- **Phase *names*.** Two objects with no shared attribute at all — the second most common
    separator in practice, and invisible to every slot-based phase, since both options occupy
    `map` and `M`. -/
theorem orth_objects_no_shared_name :
    Orth (.object {"petId", "price"} (fun _ => .req .string) .refuse)
         (.object {"petIds"} (fun _ => .req .string) .refuse) = true := by decide

/-- …and the ambiguity `docs/codec-calculus.md:711` names: **an optional binding widens
    admission**, so two objects declaring only optional names both admit the empty map and
    are not separated however disjoint their names are. -/
theorem orth_objects_optional_only :
    Orth (.object {"a"} (fun _ => .optional .string) .refuse)
         (.object {"b"} (fun _ => .optional .string) .refuse) = false := by decide

/-! ### The negatives

Each of these is a `not_sep*`/`not_uAtCan_*` witness elsewhere in the development, restated
as a demand on `Orth`. -/

/-- `not_uAtCan_array_literals`, `not_sepJV_array_literals`: `array` admits every length, so
    two arrays both admit `[]` however disjoint their elements. `Orth` answers `false` because
    both occupy `arr` and `L` — and the reason is the same one the hand witness gives, that
    the length set has to come *before* the positions. -/
theorem not_orth_array_literals :
    Orth (.array (.literal .string lsA)) (.array (.literal .string lsB)) = false := by decide

/-- `not_uAtCan_literal_string`: a literal is a refinement of its base, so its slot is its
    base's. -/
theorem not_orth_literal_string : Orth (.literal .string lsA) .string = false := by decide

/-- `not_sep_opaq_lossy_string`, `not_sep_opaq_strict_string`: `opaque` writes strings at
    either numeric policy. -/
theorem not_orth_opaq_string_lossy : Orth (.opaq true) .string = false := by decide
theorem not_orth_opaq_string_strict : Orth (.opaq false) .string = false := by decide

/-- `not_sepV_literal_heldLiteral`, `not_uAtCan_literal_held`: `held`'s `f` runs *before* the
    subterm's row, so it can move the value into any constructor and the write occupancy is
    `⊤`. Holds for every `f` and `g`, which is what makes it a phase-*opaque* case rather
    than a gap in the tables. -/
theorem not_orth_literal_held (f g : Value → Value) :
    Orth (.literal .string lsA) (.held (.literal .string lsB) f g) = false := by
  simp [Orth, Orth1, OrthM, occV, occA, occTop, occOnly, Slot.all, Member.all, specOf]

/-- Phase *alternatives* is not implemented, so `union(literal "A", literal "B")` — §5's own
    worked `ident` example, hand-discharged as `uAtCan_literal_literal` — is not certified.
    Not an unsoundness; the missing rule is disjointness of the two `ℓ`s, which the
    occupancies deliberately forget. -/
theorem not_orth_literal_literal :
    Orth (.literal .string lsA) (.literal .string lsB) = false := by decide

/-- The end-to-end shape: `uAtCan_string_null` again, from one `decide`. -/
theorem uAtCan_string_null_by_orth : UAtCan [Term.string, Term.null] :=
  uAtCan_of_orth (forall_mem_pair lawful_string lawful_null)
    (forall_mem_pair (fun _ _ _ h => nomatch h) (fun _ _ _ h => nomatch h))
    (pairwise_pair (by decide))

end Calculus
