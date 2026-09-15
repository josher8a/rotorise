import Calculus.ExactA

/-!
# Orthogonality — a decidable certificate for §5's (U)

`Typed.union` and `Obligations (.union opts)` between them carry two side conditions the
model has been discharging by hand, once per shape: `DIncomp` (§5's (D)) and `UAtAct` (§5's
residual (U)). Thirty-two `sep*`/`uAtCan_*`/`uAtAct_*` theorems live in `Discharge.lean` and
`ExactV.lean` and `ExactA.lean` — not in `Refutations.lean`, whose separation theorems are all
`not_sep*` and
are refutations rather than discharges. Twenty-five of the thirty-two are the per-shape hand
discharges; the other seven are the two generic dischargers, the ~~SepV~~→`SepJV` bridges, the
`refine`-family discharger, and the two `object` witnesses that exist in order to *fail*
(`not_uAtCan_of_sepJ`). **Thirteen of the twenty-five are the *same rule* at different
constructors**, and the by-phase table at the end of this file is that count, measured rather
than estimated.

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

Neither pair is orthogonal, and each fails on a different half. The specification's
(U) discussion
states the asymmetry for the case that *does* separate — `union(set(string), set(number))`,
where "its options write different members, so reading was never in doubt".

## The write-side slot is the `Value` constructor, not `Kind`

`Kind` collapses `strSet`, `numSet` and `binSet` to `.set`, so `κ (set string)` and
`κ (set number)` are equal and the kind disjunct of ~~SepV~~ cannot separate them. The ten
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
| alternatives | two literals, or two sets over literals, at one base with disjoint `ℓ` | `OrthL` |
| opaque predicate | `refine`'s `q`, `held`'s `f`, `custom` | undecidable by construction |

The interface the discharger consumes is `Separates`, a `Prop`; `Orth` is the *decidable*
sufficient condition for it, covering the first three phases. Phase *alternatives* is folded in
per base, and not uniform in the base. The type is the reason.
`GroundKind.number.Carrier` is `WFDouble`, a subtype of `Double`, whose `DecidableEq` is a
field of the axiomatized `numericHost`. The gate moved into the carrier and the
noncomputability did not move with it, because a `Subtype`'s instance is the base type's. So a
`Bool`-valued test for `ℓ ∩ ℓ' = ∅` uniform in the base is `noncomputable`, and `Orth` stops
reducing in the kernel, which is the whole of its value. `Domain.lean`'s note on
`GroundKind.Carrier` predicts exactly this.

`OrthL` matches the base instead. `string`, `decimal`, `boolean` and `binary` compute, and
`number` answers `false`. The same rows run one spelling further out, at
`refine(set b, each(members k ls))`, which is what `set` taking a base makes of
`set(literal k ls)`. That is the sound direction: `false` means no certificate, and a
caller at the numeric base supplies the premise to `separates_literal_disjoint` by hand, which
is `uAtCan_of_literalN_disjoint`. `null` answers `false` too, and there the answer is exact
rather than a concession: `NEFinset Unit` has one inhabitant, so two null literals hold the
same alternative and are never disjoint.

**The tag is not a phase of `Orth`, and this is a finding rather than an omission.** A
`union` option that is an object is admitted by `OptionSem.byNames` — `keysOk`, a test on the
*names* the map carries — so `select` never looks at any field's contents, discriminator
included. Two object options with disjoint `req`-literal discriminators on the same name are
therefore **not** separated at a `union`; they are separated at a `dunion`, whose options are
~~OptionSem.byTag~~ and whose (U) is a fact of its key set rather than a theorem. So the tag row of
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
def occNone {α : Type} : α → Bool := fun _ => false
def occWith {α : Type} [DecidableEq α] (x : α) (o : α → Bool) : α → Bool :=
  fun y => decide (y = x) || o y
def occBut {α : Type} [DecidableEq α] (x : α) : α → Bool := fun y => !decide (y = x)

mutual

/-- **Which value constructors this term can write.** An over-approximation of
    `{v.slot | Adm t v}`, and `occV_sound` is that containment.

    The `⊤` rows, and why each is `⊤` rather than sharper — §5's occupancy paragraph names
    the same terms:

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
      over-approximation in one place: a non-lossy `opaque` refuses a `numSet` too, since
      `opaqCodecω` budgets by the input's own depth and its element codec refuses numbers,
      and the sound direction is to keep `numSet`.
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
  -- the bottom writes nothing, so it occupies no slot
  | .never       => occNone
  | .set b       => occOnly b.slot
  | .array _     => occOnly .arr
  | .tuple _ _   => occOnly .arr
  | .record _    => occOnly .map
  | .object _   => occOnly .map
  | .dunion _  => occOnly .map
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
    arbitrary data the term carries. A lawful `r` does respect the member —
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
  -- and stores nothing, so it occupies no member
  | .never       => occNone
  | .set b       => occOnly b.member
  | .array _     => occOnly .L
  | .tuple _ _   => occOnly .L
  | .record _    => occOnly .M
  | .object _   => occOnly .M
  | .dunion _  => occOnly .M
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

    **An optional binding widens admission**, which is the ambiguity §5 names in the same
    words: two objects declaring only *optional* names both admit the empty map, so they are
    never separated here however disjoint their names.
    `orth_objects_optional_only` is that check, and it answers `false`. -/
def OrthM (x y : Term) : Bool :=
  match specOf x, specOf y with
  | some sx, some sy => reqNotDeclared sx sy || reqNotDeclared sy sx
  | _, _ => false

/-- Two alternative sets with no element in common, at a base whose equality computes.

    `∀ x ∈ ls.1, x ∉ ls'.1` and not `ls.1 ∩ ls'.1 = ∅`, because the intersection needs
    `DecidableEq` on the `Finset` and membership needs it only on the element. That matters
    here: mathlib's `DecidableEq (Finset α)` reaches `Classical.choice`, and `Orth` is a
    `by decide`. -/
def disjAlts {α : Type} [DecidableEq α] (ls ls' : NEFinset α) : Bool :=
  decide (∀ x ∈ ls.1, x ∉ ls'.1)

/-- …as the `Prop` `separates_literal_disjoint` takes. `of_decide_eq_true` and nothing more,
    which is what `disjAlts` being a `decide` of that same `Prop` buys. -/
theorem disjAlts_sound {α : Type} [DecidableEq α] {ls ls' : NEFinset α}
    (h : disjAlts ls ls' = true) : ∀ x ∈ ls.1, x ∉ ls'.1 := of_decide_eq_true h

/-- **Phase *alternatives*.** Two literals at one base whose held sets do not meet.

    The rows are the bases and not one row uniform in the base, and the file header says why:
    `GroundKind.Carrier` is `@[reducible]`, so `.string` elaborates as `String` and the
    ordinary instance applies, while `.number` elaborates as `WFDouble` and its instance is a
    field of the axiomatized `numericHost`. One uniform row would make this `noncomputable`
    and would stop `Orth` reducing at every pair, numeric or not.

    So `number` declines, and `null` declines. Both answers are `false`, and only the first is
    a concession: `NEFinset Unit` has one inhabitant, so two null literals never have disjoint
    held sets and `false` is what a complete test would answer.

    The match is on the two terms and not on a subterm, which is why
    `not_orth_array_literals` still answers `false`. A container admits its empty case
    whatever its element admits, so the rule does not propagate. A `set` is the exception,
    and `℘⁺fin` is the reason: it has no empty inhabitant, so the set rows below are the same
    rule one spelling further out rather than a container case.

    The set rows ask `b = b'` and the read side is why: `refineReads` has the base decode the
    attribute, so two bases decode one attribute to two values and the disjointness argument
    has nothing to compare. The write side would hold without it. -/
def OrthL : Term → Term → Bool
  | .literal .string ls,  .literal .string ls'  => disjAlts ls ls'
  | .literal .decimal ls, .literal .decimal ls' => disjAlts ls ls'
  | .literal .boolean ls, .literal .boolean ls' => disjAlts ls ls'
  | .literal .binary ls,  .literal .binary ls'  => disjAlts ls ls'
  -- `WFDouble`'s equality is a field of `numericHost`; see the docstring above
  | .literal .number _,   .literal .number _    => false
  -- two null literals hold the same one alternative
  | .literal .null _,     .literal .null _      => false
  -- `set(literal k ls)`, in the spelling `set` taking a base forces on it
  | .refine (.set b) (.each (.members .string ls)),
    .refine (.set b') (.each (.members .string ls'))  => decide (b = b') && disjAlts ls ls'
  | .refine (.set b) (.each (.members .decimal ls)),
    .refine (.set b') (.each (.members .decimal ls')) => decide (b = b') && disjAlts ls ls'
  | .refine (.set b) (.each (.members .binary ls)),
    .refine (.set b') (.each (.members .binary ls'))  => decide (b = b') && disjAlts ls ls'
  -- `number` declines here for the reason it declines above. `boolean` and `null` have no row
  -- because no set holds them: `liftQ (inL .boolean ls)` is `false` at every wire family, so
  -- such a term admits nothing and there is no pair to certify.
  | _, _ => false

/-- **The classifier.** A syntactic, decidable certificate that two terms cannot both admit
    one input — on both halves of the pair. `false` means "no certificate found". -/
def Orth (x y : Term) : Bool := Orth1 x y || OrthM x y || OrthL x y

/-! ## Soundness

Two structural recursions, one per side, each mutual with a list companion for `union`. The
statement is about the **rows** (`Adm`/`AdmA`) and about `admitOptV`/`admitOptA`, never about
the term's own rows: `select` filters by the *option* semantics, and for an object option that is
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
    ∃ b, t = .object b := by
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
      obtain ⟨b, rfl⟩ := specOf_some_object hs
      cases v <;> simp_all [admitOptV, specOf, occV, occOnly, Value.slot]

/-- **A refusing `opaque` writes no numeral**, off the joint row.

    The occupancy proofs below are the only consumers, and they used to reach this fact
    through ~~Adm_opaq_eq_adm~~ into the retired per-aspect tables — which made the whole
    `Orth` chain a dependent of them, in the proof rather than in any statement. Both rows
    ask `opaqCodecω`, so the fact is stated here now and the chain owes them nothing. -/
theorem Adm_opaq_false_num (d : Double) : Adm (.opaq false) (.num d) = false := by
  show ((opaqCodec (0+1) false).e (.num d)).isSome = false
  rw [opaqCodec_e_num]; rfl

/-- …and its twin on the read side. -/
theorem AdmA_opaq_false_n (x : WFNumeral) : AdmA (.opaq false) (.n x) = false := by
  show ((opaqCodec (0+1) false).p (.n x)).isSome = false
  rw [opaqCodec_p_n]; rfl

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

    `opaq false` is the one case that appeals to a lemma rather than to the row directly
    (`Adm_opaq_false_num` above), and the lemma is available because the row asks the
    codec. -/
theorem occV_sound : ∀ (t : Term), OccSoundV t
  -- The rows whose `Adm` is a kind test and nothing more: one group, because a per-row
  -- proof here would be seven copies of one simp set. `number` and `decimal` are separate
  -- only because their gates (`inD`, `isStored`) have to be in the set.
  | .string | .boolean | .binary | .null =>
      fun v h => by cases v <;> simp_all [Adm, occV, occOnly, Value.slot]
  | .number => fun v h => by cases v <;> simp_all [Adm, inD, occV, occOnly, Value.slot]
  -- the row is `false`, so the premise is the one that cannot arrive
  | .never => fun _ h => by simp [Adm] at h
  | .decimal => fun v h => by cases v <;> simp_all [Adm, isStored, occV, occOnly, Value.slot]
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
  -- the containers, whose slot is fixed by the constructor and not by the payload
  | .array _ | .tuple _ _ | .record _ =>
      fun v h => by cases v <;> simp_all [Adm, occV, occOnly, Value.slot]
  -- the key set is non-empty, so a value with no tag at one key has no assignment at all;
  -- over an empty key set every value would carry the empty assignment and pass the guard
  | .dunion m => fun v h => by
      obtain ⟨k, hk⟩ := m.ks.2
      have hnone : ∀ w : Value, tagAtV k w = none → tagOfV m.ks.1 w = none :=
        fun w hw => dif_neg fun hall => by
          have hk' := hall k hk; rw [hw] at hk'; simp at hk'
      cases v <;> simp_all [Adm, tagAtV, occV, occOnly, Value.slot]
  | .object (.mk _ _ _) => fun v h => by
      cases v <;> simp_all [Adm, AdmBody, occV, occOnly, Value.slot]
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
            | (exact absurd h (by simp [Adm_opaq_false_num]))

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
  -- One group where the write side needs three: on the read side the gates are gone, the
  -- stored member being what `Attr.member` already computes.
  | .string | .number | .decimal | .boolean | .binary | .null =>
      fun a h => by cases a <;> simp_all [AdmA, occA, occOnly, Attr.member]
  | .never => fun _ h => by simp [AdmA] at h
  | .literal k _ => fun a h => by
      rw [AdmA_literal] at h
      cases k with
      | decimal => simp [occA, occOnly, GroundKind.member, admALit_decimal_member h]
      | _ => cases a <;> simp_all [AdmALit, occA, occOnly, Attr.member, GroundKind.member]
  | .set b => fun a h => by
      cases b <;> cases a <;>
        simp_all [AdmA, AdmASet, occA, occOnly, Attr.member, SetBase.member]
  | .array _ | .tuple _ _ | .record _ =>
      fun a h => by cases a <;> simp_all [AdmA, occA, occOnly, Attr.member]
  | .object (.mk _ _ _) => fun a h => by
      cases a <;> simp_all [AdmA, AdmABody, occA, occOnly, Attr.member]
  | .dunion m => fun a h => by
      obtain ⟨k, hk⟩ := m.ks.2
      have hnone : ∀ b : Attr, tagAtA k b = none → tagOfA m.ks.1 b = none :=
        fun b hb => dif_neg fun hall => by
          have hk' := hall k hk; rw [hb] at hk'; simp at hk'
      cases a <;> simp_all [AdmA, tagAtA, occA, occOnly, Attr.member]
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
            | (exact absurd h (by simp [AdmA_opaq_false_n]))

theorem occA_soundL : ∀ (ts : List Term), OccSoundAL ts
  | [] => trivial
  | t :: ts => ⟨occA_sound t, occA_soundL ts⟩
end

/-! ## Discharging (U)

The families each option is confined to are the occupancy **intersected with the option's own
admission**. That is the move the retired per-aspect layer made with its own footprint
definitions, and it is what lets one pair of families serve every phase: disjointness in either factor makes the intersection disjoint, so
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

theorem orthSV_disjoint {x y : Term} (h : (Orth1 x y || OrthM x y) = true) :
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

theorem orthSA_disjoint {x y : Term} (h : (Orth1 x y || OrthM x y) = true) :
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

/-- **What the discharger consumes.** Both families disjoint, as a `Prop` — the interface, of
    which `Orth` is the decidable part and the numeric base of phase *alternatives* the part
    that cannot be.

    Naming it is what keeps one discharger: a new phase is a new theorem producing
    `Separates`, not a new case in `uAtCan_of_separated`. -/
def Separates (x y : Term) : Prop :=
  (∀ v, OrthSV x v → ¬ OrthSV y v) ∧ (∀ a, OrthSA x a → ¬ OrthSA y a)

/-! ## Phase *alternatives*

Two literals at one base with disjoint held sets. The `Prop` below is uniform in the base and
`OrthL` decides it at four of the six, for the reason the file header gives. It is the
generalization of the hand instances at one base: `uAtCan_of_literalN_disjoint` in
`Discharge.lean` is one of them, and is now the caller that supplies the premise where `OrthL`
declines. Its siblings at the string base went with the per-aspect layer, this phase being
what reaches them. -/

/-- Disjoint held sets make `inL` disjoint, at every base. Two bases are not the pattern
    match:

    * `null` — `inL .null _ .null` is `true` unconditionally, so two null literals are never
      disjoint. The premise is what rules it out, *vacuously*: `NEFinset Unit` has exactly one
      inhabitant, so `ls` and `ls'` both contain `()` and `hd` is uninhabited. The rule needs
      no `k ≠ .null` side condition.
    * `decimal` — membership goes *through* the `Numeral.Stored` gate rather than round it, so
      the proof is a `split` on the `dite` rather than a rewrite. `by_cases` would reach
      `Classical.em`; `split` does not. -/
theorem inL_disjoint {k : GroundKind} {ls ls' : NEFinset k.Carrier}
    (hd : ∀ x ∈ ls.1, x ∉ ls'.1) (v : Value) (h : inL k ls v = true) : inL k ls' v = false := by
  cases k with
  | string =>
    cases v with
    | str s =>
      replace h : decide (s ∈ ls.1) = true := h
      exact decide_eq_false (hd s (of_decide_eq_true h))
    | _ => rfl
  | number =>
    cases v with
    | num d =>
      -- `number` joined `decimal` in splitting on its carrier's gate
      cases hw : Numeral.WF d.toDec with
      | false => simp [inL, hw] at h
      | true =>
        simp only [inL, hw, dite_true, decide_eq_true_eq] at h
        simp only [inL, hw, dite_true]
        exact decide_eq_false (hd ⟨d, hw⟩ h)
    | _ => rfl
  | boolean =>
    cases v with
    | bool b =>
      replace h : decide (b ∈ ls.1) = true := h
      exact decide_eq_false (hd b (of_decide_eq_true h))
    | _ => rfl
  | binary =>
    cases v with
    | bin b =>
      replace h : decide (b ∈ ls.1) = true := h
      exact decide_eq_false (hd b (of_decide_eq_true h))
    | _ => rfl
  | null =>
    cases v with
    | null =>
      obtain ⟨u, hu⟩ := ls.2
      obtain ⟨u', hu'⟩ := ls'.2
      exact absurd (by cases u; cases u'; exact hu') (hd u hu)
    | _ => rfl
  | decimal =>
    cases v with
    | str s =>
      show (if hst : Numeral.Stored s = true then
              decide ((⟨s, hst⟩ : StoredNumeral) ∈ ls'.1) else false) = false
      replace h : (if hs : Numeral.Stored s = true then
              decide ((⟨s, hs⟩ : StoredNumeral) ∈ ls.1) else false) = true := h
      split
      · rename_i hst
        rw [dif_pos hst] at h
        exact decide_eq_false (hd _ (of_decide_eq_true h))
      · rfl
    | _ => rfl

theorem denote_lit (k : GroundKind) (ls : NEFinset k.Carrier) :
    denote (.literal k ls) = literalCodec k ls := rfl

/-- The literal's read row *is* the codec's read domain — `AdmA_exact` with no hypothesis, so
    this is a rewrite rather than a discharge. It is what makes the read side of the rule
    uniform in the base: `AdmALit` is spelled per base (and at `decimal` it asks the codec),
    but the domain is `(baseCodec k).restrict (inL k ls)` at every base. -/
theorem admALit_iff {k : GroundKind} {ls : NEFinset k.Carrier} {a : Attr} :
    AdmALit k ls a = true ↔ ((literalCodec k ls).p a).isSome = true := by
  rw [← denote_lit k ls, ← AdmA_literal k ls a]
  exact AdmA_exact (.literal k ls) a

/-- …and so the read side is the same `inL` disjointness, one level up: the base reads the
    attribute to *one* value, and one value cannot be in two disjoint held sets.

    This was the read-side argument the retired ~~SepA~~ instance made at a literal, and the
    reason §5 recorded the readable side as "undischargeable from the tables alone" was that
    the old `admALit .number` row was `⊤`. The row asks now, and this is where the argument
    lives. -/
theorem admALit_disjoint {k : GroundKind} {ls ls' : NEFinset k.Carrier}
    (hd : ∀ x ∈ ls.1, x ∉ ls'.1) (a : Attr)
    (h : AdmALit k ls a = true) : AdmALit k ls' a = false := by
  obtain ⟨v, hp⟩ := Option.isSome_iff_exists.mp (admALit_iff.mp h)
  rw [literalCodec_p_restrict] at hp
  obtain ⟨hbase, hin⟩ := restrict_p.mp hp
  cases hq : AdmALit k ls' a with
  | false => rfl
  | true =>
    obtain ⟨v', hp'⟩ := Option.isSome_iff_exists.mp (admALit_iff.mp hq)
    rw [literalCodec_p_restrict] at hp'
    obtain ⟨hbase', hin'⟩ := restrict_p.mp hp'
    rw [hbase] at hbase'
    obtain rfl : v = v' := Option.some.inj hbase'
    rw [inL_disjoint hd v hin] at hin'
    exact absurd hin' (by simp)

/-- **Phase *alternatives*.** Uniform in the base, both sides, no lawfulness premise and no
    `ident` conjunct — where §5 stated its second disjunct as
    `ident(cᵢ) ∧ ident(cⱼ) ∧ adm(cᵢ) ∩ adm(cⱼ) = ∅`. -/
theorem separates_literal_disjoint {k : GroundKind} {ls ls' : NEFinset k.Carrier}
    (hd : ∀ x ∈ ls.1, x ∉ ls'.1) :
    Separates (.literal k ls) (.literal k ls') := by
  refine ⟨?_, ?_⟩
  · rintro v ⟨-, hx⟩ ⟨-, hy⟩
    rw [specOf_none_admitOptV rfl, Adm_literal] at hx hy
    -- `AdmLit` is `inL`, full stop, since `number`'s `WF` conjunct became its carrier's
    have hix : inL k ls v = true := hx
    have hiy : inL k ls' v = true := hy
    rw [inL_disjoint hd v hix] at hiy
    exact absurd hiy (by simp)
  · rintro a ⟨-, hx⟩ ⟨-, hy⟩
    rw [specOf_none_admitOptA rfl, AdmA_literal] at hx hy
    rw [admALit_disjoint hd a hx] at hy
    exact absurd hy (by simp)

/-! ### …and the same rule one spelling further out

`set` takes a base, so a set over a literal is a **restriction of the set**:
`refine(set b, each(members k ls))`, and `setCodec_restrict` proves the two are one pair.
`sepJV_set_literals` is that separation at one pair of alternatives, on the write side.
These two are the rule, uniform in the base and on both halves. -/

/-- **A wire set cannot pass two disjoint held sets**, and `℘⁺fin` is the whole of it: the
    set has an element, and one element is not in both.

    The nonemptiness is what makes this a `set` fact rather than a container fact. An `array`
    admits `[]`, which passes every element predicate vacuously, and that is exactly why
    `not_uAtCan_array_literals` holds and `uAtAct_array_literals` is the most that pair
    meets. -/
theorem liftQ_inL_disjoint {k : GroundKind} {ls ls' : NEFinset k.Carrier}
    (hd : ∀ x ∈ ls.1, x ∉ ls'.1) (v : Value)
    (h : liftQ (inL k ls) v = true) : liftQ (inL k ls') v = false := by
  cases v with
  | strSet S =>
      obtain ⟨x, hx⟩ := S.2
      simp only [liftQ, decide_eq_true_eq] at h
      simp only [liftQ, decide_eq_false_iff_not]
      exact fun hall => by
        have hne := inL_disjoint hd (.str x) (h x hx)
        rw [hall x hx] at hne
        exact absurd hne (by simp)
  | numSet S =>
      obtain ⟨x, hx⟩ := S.2
      simp only [liftQ, decide_eq_true_eq] at h
      simp only [liftQ, decide_eq_false_iff_not]
      exact fun hall => by
        have hne := inL_disjoint hd (.num x) (h x hx)
        rw [hall x hx] at hne
        exact absurd hne (by simp)
  | binSet S =>
      obtain ⟨x, hx⟩ := S.2
      simp only [liftQ, decide_eq_true_eq] at h
      simp only [liftQ, decide_eq_false_iff_not]
      exact fun hall => by
        have hne := inL_disjoint hd (.bin x) (h x hx)
        rw [hall x hx] at hne
        exact absurd hne (by simp)
  | _ => exact absurd h (by simp [liftQ])

/-- `Adm`'s and `AdmA`'s `refine` rows, named here because this proof is the only caller and
    the rows are otherwise read off the definition. -/
theorem Adm_refine_row (t : Term) (p : Pred) (v : Value) :
    Adm (.refine t p) v = (Adm t v && p.eval v) := rfl

/-- …and the read row, where the predicate is asked of what the base *decoded*, which is what
    `refineReads` names. -/
theorem AdmA_refine_row (t : Term) (p : Pred) (a : Attr) :
    AdmA (.refine t p) a = (AdmA t a && refineReads t p.eval a) := rfl

/-- **Phase *alternatives* at a set.** Two sets over disjoint literals, at one set base.

    The base has to be the same on both sides, and the read side is the reason: `refineReads`
    asks the base to decode the attribute, so two different bases decode one attribute to two
    different values and the disjointness argument has nothing to compare. On the write side
    the bases could differ and the rule would still hold, which is a sharpening nothing wants
    — `Orth1` already separates two set bases whose members differ. -/
theorem separates_setLiteral_disjoint {b : SetBase} {k : GroundKind}
    {ls ls' : NEFinset k.Carrier} (hd : ∀ x ∈ ls.1, x ∉ ls'.1) :
    Separates (.refine (.set b) (.each (.members k ls)))
              (.refine (.set b) (.each (.members k ls'))) := by
  refine ⟨?_, ?_⟩
  · rintro v ⟨-, hx⟩ ⟨-, hy⟩
    rw [specOf_none_admitOptV rfl, Adm_refine_row] at hx hy
    have hlx : liftQ (inL k ls) v = true := (Bool.and_eq_true_iff.mp hx).2
    have hly : liftQ (inL k ls') v = true := (Bool.and_eq_true_iff.mp hy).2
    rw [liftQ_inL_disjoint hd v hlx] at hly
    exact absurd hly (by simp)
  · rintro a ⟨-, hx⟩ ⟨-, hy⟩
    rw [specOf_none_admitOptA rfl, AdmA_refine_row] at hx hy
    have hrx := (Bool.and_eq_true_iff.mp hx).2
    have hry := (Bool.and_eq_true_iff.mp hy).2
    -- one base, so one decoded value: `refineReads` is `false` where the base reads nothing
    cases hp : (denote (Term.set b)).p a with
    | none => rw [refineReads_none hp] at hrx; exact absurd hrx (by simp)
    | some v =>
        rw [refineReads_some hp] at hrx hry
        simp only [Pred.eval] at hrx hry
        rw [liftQ_inL_disjoint hd v hrx] at hry
        exact absurd hry (by simp)

/-- Phase *alternatives*, from its decidable half. One `split` over `OrthL`'s ten rows: four
    hand `separates_literal_disjoint` its premise, three hand `separates_setLiteral_disjoint`
    its premise and the base equality the read side needs, and three answer `false`. -/
theorem separates_of_orthL {x y : Term} (h : OrthL x y = true) : Separates x y := by
  unfold OrthL at h
  split at h
  · exact separates_literal_disjoint (disjAlts_sound h)
  · exact separates_literal_disjoint (disjAlts_sound h)
  · exact separates_literal_disjoint (disjAlts_sound h)
  · exact separates_literal_disjoint (disjAlts_sound h)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · obtain ⟨hb, hdis⟩ := Bool.and_eq_true_iff.mp h
    obtain rfl := of_decide_eq_true hb
    exact separates_setLiteral_disjoint (disjAlts_sound hdis)
  · obtain ⟨hb, hdis⟩ := Bool.and_eq_true_iff.mp h
    obtain rfl := of_decide_eq_true hb
    exact separates_setLiteral_disjoint (disjAlts_sound hdis)
  · obtain ⟨hb, hdis⟩ := Bool.and_eq_true_iff.mp h
    obtain rfl := of_decide_eq_true hb
    exact separates_setLiteral_disjoint (disjAlts_sound hdis)
  · exact absurd h (by simp)

/-- **The whole premise the discharger takes**, as one name: every pair of options separated.

    `Separates` is the rule for a pair and this is the rule for a list, so a phase produces the
    first and a caller supplies the second. `separated_of_orth` below is the only bridge the
    classifier needs, where before every discharger wrote `h.imp separates_of_orth` itself.

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

theorem separates_of_orth {x y : Term} (h : Orth x y = true) : Separates x y := by
  rcases Bool.or_eq_true_iff.mp h with h' | hl
  · exact ⟨orthSV_disjoint h', orthSA_disjoint h'⟩
  · exact separates_of_orthL hl

/-- **§5's (U), from pairwise separation.** The two other premises are the ones every
    discharger in `Discharge.lean` already takes: lawfulness, which soundness supplies, and
    the closed-object restriction.

    `hcl` is `Term.isOpenObject`, one decidable question about the payload, where the
    premise used to be three quantifiers and a disequality against a three-argument
    constructor. It is not a defect being worked around: an object option with an open rest
    (`.codec t`) has `Adm t v = true` where `admitOptV … v = false` — the option refuses maps
    its own `e` accepts — and §5 argues that this is the intended reading ("an object's open
    part is unreachable through a union — the price of deciding by names").
    `optionSem_self_admit` takes the same premise for the same reason. `Orth`
    declines to certify such an option rather than proposing a repair. -/
theorem uAtCan_of_separated {opts : List Term}
    (hlaw : ∀ t ∈ opts, Lawful (denote t))
    (hcl : ∀ t ∈ opts, t.isOpenObject = false)
    (h : Separated opts) :
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
  · rw [List.pairwise_map]; exact h.imp (fun hs => hs.1)
  · rw [List.pairwise_map]; exact h.imp (fun hs => hs.2)
  · refine List.forall_mem_map.mpr fun t ht v a he => ?_
    rw [optionSemOf_c] at he
    exact optionSem_self_admit t (hcl t ht) (hlaw t ht) he

/-- The classifier's answer for a whole option list, which is the one bridge from the decidable
    phase to the `Prop` the discharger takes. -/
theorem separated_of_orth {opts : List Term}
    (h : List.Pairwise (fun x y => Orth x y = true) opts) : Separated opts :=
  h.imp separates_of_orth

/-- …and from the decidable premise alone, which reaches six of the twenty-five hand
    discharges; seven more need `Separates` and `uAtCan_of_separated` above, for thirteen of
    twenty-five between them. The by-phase table at the end of the file is the measurement. -/
theorem uAtCan_of_orth {opts : List Term}
    (hlaw : ∀ t ∈ opts, Lawful (denote t))
    (hcl : ∀ t ∈ opts, t.isOpenObject = false)
    (h : List.Pairwise (fun x y => Orth x y = true) opts) :
    UAtCan opts :=
  uAtCan_of_separated hlaw hcl (separated_of_orth h)

/-- …and the residue the laws actually need. -/
theorem uAtAct_of_orth {opts : List Term}
    (hlaw : ∀ t ∈ opts, Lawful (denote t))
    (hcl : ∀ t ∈ opts, t.isOpenObject = false)
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
theorem orth_string_dunion :
    Orth .string (.dunion ⟨⟨{"k"}, Finset.singleton_nonempty "k"⟩, ∅, fun k => nomatch k.2⟩)
      = true := by decide
theorem orth_array_record : Orth (.array .string) (.record .string) = true := by decide

/-- §5's worked `(set)` example, and out of reach of ~~SepV~~'s kind disjunct: `κ` collapses
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
    Orth (.object (.mk {"petId", "price"} (fun _ => .req .string) .refuse))
         (.object (.mk {"petIds"} (fun _ => .req .string) .refuse)) = true := by decide

/-- …and the ambiguity §5 names: **an optional binding widens admission**, so two objects
    declaring only optional names both admit the empty map and are not separated however
    disjoint their names are. -/
theorem orth_objects_optional_only :
    Orth (.object (.mk {"a"} (fun _ => .optional .string) .refuse))
         (.object (.mk {"b"} (fun _ => .optional .string) .refuse)) = false := by decide

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

/-- `opaque` writes strings at either numeric policy — the fact the retired layer's two
    `opaque`-against-`string` refutations carried, kept here where it is decidable. -/
theorem not_orth_opaq_string_lossy : Orth (.opaq true) .string = false := by decide
theorem not_orth_opaq_string_strict : Orth (.opaq false) .string = false := by decide

/-- `not_uAtCan_literal_held`: `held`'s `f` runs *before* the
    subterm's row, so it can move the value into any constructor and the write occupancy is
    `⊤`. Holds for every `f` and `g`, which is what makes it a phase-*opaque* case rather
    than a gap in the tables. -/
theorem not_orth_literal_held (f g : Value → Value) :
    Orth (.literal .string lsA) (.held (.literal .string lsB) f g) = false := by
  simp [Orth, Orth1, OrthM, OrthL, occV, occA, occTop, occOnly, Slot.all, Member.all, specOf]

/-- **Phase *alternatives*, and §5's own worked `ident` example.** The occupancies forget
    `ℓ`, so `Orth1` answers `false` here; `OrthL` reads `ℓ` and the classifier certifies the
    pair. This is the pair `src/`'s `union` accepts through its `identifies` exemption, and
    the certificate now reaches it. -/
theorem orth_literal_literal :
    Orth (.literal .string lsA) (.literal .string lsB) = true := by decide

/-- …and the same two alternatives, not disjoint. The test reads `ℓ`, so it answers the
    question rather than the shape. -/
theorem not_orth_literal_literal_same :
    Orth (.literal .string lsA) (.literal .string lsA) = false := by decide

/-- **The numeric base declines, and the pair is still not ambiguous.** `WFDouble`'s equality
    is a field of `numericHost`, so `OrthL` has no computable row there and answers `false`.
    `separates_literal_disjoint` takes the premise by hand instead, which is
    `uAtCan_of_literalN_disjoint`'s content. -/
theorem not_orth_literal_number (ls ls' : NEFinset GroundKind.number.Carrier) :
    Orth (.literal .number ls) (.literal .number ls') = false := by
  simp [Orth, Orth1, OrthM, OrthL, occV, occA, occOnly, Slot.all, Member.all, specOf,
    GroundKind.slot, GroundKind.member]

/-- **Two null literals are never disjoint**, and `false` here is exact rather than a
    concession: `NEFinset Unit` has one inhabitant, so both hold `()`. -/
theorem not_orth_literal_null (ls ls' : NEFinset GroundKind.null.Carrier) :
    Orth (.literal .null ls) (.literal .null ls') = false := by
  simp [Orth, Orth1, OrthM, OrthL, occV, occA, occOnly, Slot.all, Member.all, specOf,
    GroundKind.slot, GroundKind.member]

/-- **The same rule at a set**, which is the pair `Separation.lean` discharges by hand as
    `sepJV_set_literals` — and only on the write side, `SepJV` being about `Adm`. The
    certificate answers both halves. `℘⁺fin` is what makes it a `set` fact: the payload has an
    element, and one element is not in two disjoint held sets. -/
theorem orth_set_literals :
    Orth (.refine (.set .string) (.each (.members .string lsA)))
         (.refine (.set .string) (.each (.members .string lsB))) = true := by decide

/-- …and not where the alternatives meet. -/
theorem not_orth_set_literals_same :
    Orth (.refine (.set .string) (.each (.members .string lsA)))
         (.refine (.set .string) (.each (.members .string lsA))) = false := by decide

/-- **Two set bases decline**, and the read side is the reason: `refineReads` has the base
    decode the attribute, so two bases decode one attribute to two values and there is
    nothing to compare. `set(string)` and `set(decimal)` are the pair that shows it, both
    writing a `strSet` while storing `SS` and `NS`. -/
theorem not_orth_set_literals_two_bases :
    Orth (.refine (.set .string) (.each (.members .string lsA)))
         (.refine (.set .decimal) (.each (.members .string lsB))) = false := by decide

/-- **A `closure` beside a `members` is not certified**, which is the case `Pred` keeps rather
    than removes. Holds for every `q`, so this is phase *opaque predicate* and not a gap. -/
theorem not_orth_set_literal_closure (q : Value → Bool) :
    Orth (.refine (.set .string) (.each (.members .string lsA)))
         (.refine (.set .string) (.each (.closure q))) = false := by
  simp [Orth, Orth1, OrthM, OrthL, occV, occA, occOnly, Slot.all, Member.all, specOf,
    SetBase.slot, SetBase.member]

/-- …and the pair, discharged from one `decide` where it used to name its premise. At
    `.number` the route is still `separates_literal_disjoint` with the premise proved by
    hand, `DecidableEq Double` being noncomputable; that is `uAtCan_of_literalN_disjoint`'s
    content, generalized. -/
theorem uAtCan_literal_literal_by_orth :
    UAtCan [Term.literal .string lsA, Term.literal .string lsB] :=
  uAtCan_of_orth (forall_mem_pair (lawful_literal _ _) (lawful_literal _ _))
    (forall_mem_pair rfl rfl)
    (List.pairwise_pair.mpr (by decide))

/-! ### The existing discharges, by phase

Where the hand proofs sit, and the two that sit nowhere. `Orth` is the decidable part, and
`Separates` covers what is left of phase *alternatives*; the last column says which.

| theorem | phase | reached |
| --- | --- | --- |
| `uAtCan_of_literalN_disjoint` | alternatives | `separates_literal_disjoint`, the base `OrthL` declines |
| `uAtCan_of_refine_disjoint`, `uAtCan_boolLiterals`, `uAtCan_refine_container` | opaque predicate | never — `q` is arbitrary |
| `sepJV_set_literals` | alternatives | `OrthL`'s set rows, and on both halves where the hand proof is `SepJV` |
| ~~uAtCan_dunion~~ | tag | a different constructor, and no longer a theorem: its key set makes the fact |
| `uAtCan_opaque` | kind | one level below the term language |
| `uAtAct_array_literals` | none: `UAtCan` itself is false | never — there is nothing to certify |

**The rows that are gone were the reason this table was worth having.** Every discharge in
phase *slot*, and the string-base half of phase *alternatives*, was a hand proof stated on the
per-aspect ~~SepV~~/~~SepA~~ and reached here by `decide` — so when that layer was retired the
hand proofs went with it and this file is what certifies those pairs now. Three more went with
the four tables: ~~sep_lazy_literal~~, ~~sepA_lazy_literal~~ and ~~sep_nullable_plain~~ were
stated on the retired rows, and each said that a transparent wrapper — `lazy`, `nullable` over a
literal — separates from a plain literal exactly as the subterm does. Nothing consumed them,
and `Adm` and `AdmA` pass through both wrappers by definition, so the fact is the rows' rather
than a theorem's. What is left is the two phases `Orth` does *not* reach, the numeric base of
phase *alternatives*, and the two constructors below the term language: the table has stopped
being a map of duplicated work and is now a list of what only exists by hand.

**Two fit no phase of the classifier, and each is a limit worth naming** — a different limit
from the row above them, where the phase is `none` because `UAtCan` is false and there is no
orthogonality to certify at all.

`sepJA_legacy_decimal` separates `legacy(string, r)` from `decimal` by the **member**, and
`Orth` cannot: `occA (.legacy _ _)` is `⊤` because the *row* is
`AdmA t a || (r a).isSome` with `r` arbitrary data, while `μSyn (.legacy t _) = μSyn t` is
sharper — true of the lawful codec, false of the row. `sepJA_needs_member` is the pair
showing `AdmA` alone does not separate them either. So the member disjunct of `SepJA` is not
subsumed here, and a phase that reached it would have to take `ReadsCoherently` as a premise.

`uAtAct_array_literals` is out of reach **by strength, not by phase**: `Orth` produces
`UAtCan`, and that pair genuinely fails `UAtCan` (`not_uAtCan_array_literals` — both options
admit `[]`) while meeting `UAtAct`, because the *union* declines the empty array. Nothing that
holds only where the union acts can be certified per-option, which is what a syntactic
certificate on a pair of terms is. That gap is where the working container schemas sit. -/

/-- The end-to-end shape, from one `decide` — and since the hand proof it used to restate
    was retired with the per-aspect layer, this is now where `UAtCan [string, null]` is
    established rather than a second route to it. -/
theorem uAtCan_string_null_by_orth : UAtCan [Term.string, Term.null] :=
  uAtCan_of_orth (forall_mem_pair lawful_string lawful_null)
    (forall_mem_pair rfl rfl)
    (List.pairwise_pair.mpr (by decide))

end Calculus
