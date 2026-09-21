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
`refine`-family discharger, and the two `object` witnesses that existed in order to *fail*.
**Thirteen of the twenty-five are the *same rule* at different
constructors**, and the by-phase table at the end of this file is that count, measured rather
than estimated.

`Orth` is that rule, written once. It is a **phase classifier**: given a pair of terms it
answers whether there is a *syntactic certificate* that they cannot both admit one input.

## Sound, never complete, and why there is no `unknown`

Semantic orthogonality is undecidable in this language — `refine t q` carries an arbitrary
`Value → Bool` and `held t f g` an arbitrary pair of maps. So `Orth` answers a *narrower* question, and the answer `false` means "no
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
| names | the presence each body admits at one name, where the two meet at the bottom | `OrthM` |
| literals | one shared required name pinned to disjoint alternatives, at four bases | `OrthS` |
| alternatives | two literals, or two sets over literals, at one base with disjoint `ℓ` | `OrthL` |
| opaque predicate | `refine`'s `q`, `held`'s `f` | undecidable by construction |

The interface the discharger consumes is `Separates`, a `Prop`; `Orth` is the *decidable*
sufficient condition for it, covering the first four phases. Phases *literals* and
*alternatives* are folded in per base, and not uniform in the base. The type is the reason.
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

**The tag is a phase, and phase *literals* is it.** A `union` option that is an object is
admitted by `OptionSem.byStructure`: the names lie in the spec's interval, *and* every present
name whose field is a literal carries one of that literal's alternatives. So `select` does read
the discriminating fields, and two object options with disjoint `req`-literal alternatives on
one shared name are separated at a `union`.

A dissection is then a **certified `union`** of its members: a union whose members no two of
whose structures meet. A tag table keyed by the discriminating literals is an index the host
builds over such a union, and it is an optimisation rather than the operation.

Phase *literals* takes four bases where a tag takes two, and the reason is the difference between
the two questions. A tag rule is about what a key can carry, and a tag is read back as text, so
`string` and `decimal` are the bases that can carry one. The meet is about what a value can
satisfy, and a `boolean` or `binary` literal separates two objects as well as any. `number` and
`null` decline here for the reasons `OrthL` gives at the same two bases.
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
    * `refine t q` — the subterm's, over-approximating away `q`. Sound: a refinement writes
      a subset of what the base writes.
    * `LegacyRead` is outside the structural classifier.
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
  -- `array` and `tuple` are one shape now, and both rows said the same thing
  | .list _ _ _  => occOnly .arr
  | .object _   => occOnly .map
  | .held _ _ _  => occTop
  | .refine t _  => occV t
  | .lazy t      => occV t
  | .union opts  => occVL opts
  | .opaq lossy  => if lossy then occTop else occBut .num

def occVL : List Term → Slot → Bool
  | [] => fun _ => false
  | t :: ts => fun s => occV t s || occVL ts s
end

mutual

/-- **Which members this term can read.** The mirror, and it is not a symmetric mirror:
    `held` has distinct write and read rows.

    `LegacyRead` is not a `Term`. The classifier has no alternate-reader row. -/
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
  | .list _ _ _  => occOnly .L
  | .object _   => occOnly .M
  | .refine t _  => occA t
  | .held t _ _  => occA t
  | .lazy t      => occA t
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

/-- **The two bodies admit presences at one name that meet at the bottom.**

    `keysOk` says the key set lies inside the presence the spec admits at each name. Two
    options are separated at a name when the presence each admits there meets at the bottom:
    no key set can lie inside both, because a key set either carries the name or omits it and
    the meet refuses each answer.

    Presence is the lattice `Bool × Bool` and the meet is componentwise, so the test is the
    two conjunctions being `false`.

    **The quantifier runs over the names one side declares, and that is complete.** At a name
    neither side declares, each side answers the top or `(false, true)`, and neither meet of
    those is the bottom. `presenceMeetsBot_undeclared_false` below is that claim, proved.

    Two existentials over the two declared sets and not one over their union: the union needs
    `DecidableEq (Finset Name)`, whose mathlib instance reaches `Classical.choice`, and `Orth`
    is a `by decide`. Membership needs equality on the element alone. -/
def presenceMeetsBot (sx sy : BodySpec) (k : Name) : Bool :=
  !((sx.presenceAt k).1 && (sy.presenceAt k).1) &&
  !((sx.presenceAt k).2 && (sy.presenceAt k).2)

/-- The separator: some name one side declares meets at the bottom. -/
def namesSeparate (sx sy : BodySpec) : Bool :=
  decide (∃ k : {k // k ∈ sx.names.1}, presenceMeetsBot sx sy k.1 = true) ||
  decide (∃ k : {k // k ∈ sy.names.1}, presenceMeetsBot sx sy k.1 = true)

/-- **Quantifying over the declared names is complete.** A name neither side declares can never
    meet at the bottom: each side answers `(true, true)` under a block and `(false, true)`
    without one, and every one of the four meets keeps the absent bit. -/
theorem presenceMeetsBot_undeclared_false {sx sy : BodySpec} {k : Name}
    (hx : k ∉ sx.names.1) (hy : k ∉ sy.names.1) : presenceMeetsBot sx sy k = false := by
  have ex : sx.presenceAt k = if sx.wild.isSome then (true, true) else (false, true) := by
    simp only [BodySpec.presenceAt, MapOf.at, dif_neg hx]
  have ey : sy.presenceAt k = if sy.wild.isSome then (true, true) else (false, true) := by
    simp only [BodySpec.presenceAt, MapOf.at, dif_neg hy]
  simp only [presenceMeetsBot, ex, ey]
  cases sx.wild.isSome <;> cases sy.wild.isSome <;> rfl

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
  | some sx, some sy =>
      namesSeparate sx sy
  | _, _ => false

/-- Two alternative sets with no element in common, at a base whose equality computes.

    `∀ x ∈ ls.1, x ∉ ls'.1` and not `ls.1 ∩ ls'.1 = ∅`, because the intersection needs
    `DecidableEq` on the `Finset` and membership needs it only on the element. That matters
    here: mathlib's `DecidableEq (Finset α)` reaches `Classical.choice`, and `Orth` is a
    `by decide`.

    **A literal has no set and this is not its test.** `Pred.members` is the remaining set of
    alternatives: a refinement predicate is data over a `Finset`, so the `set` rows below still
    compare two sets. A literal carries one value, and its rows compare two values. -/
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

    So `number` declines, and its answer is `false`. `null` no longer needs a row of its own:
    `Unit` has one inhabitant, so `decide (x ≠ y)` computes `false` there, which is what a
    complete test answers. The concession the old row carried is gone rather than restated.

    The match is on the two terms and not on a subterm, which is why
    `not_orth_array_literals` still answers `false`. A container admits its empty case
    whatever its element admits, so the rule does not propagate. A `set` is the exception,
    and `℘⁺fin` is the reason: it has no empty inhabitant, so the set rows below are the same
    rule one spelling further out rather than a container case.

    The set rows ask `b = b'` and the read side is why: `refineReads` has the base decode the
    attribute, so two bases decode one attribute to two values and the disjointness argument
    has nothing to compare. The write side would hold without it. -/
def OrthL : Term → Term → Bool
  | .literal .string x,  .literal .string y  => decide (x ≠ y)
  | .literal .decimal x, .literal .decimal y => decide (x ≠ y)
  | .literal .boolean x, .literal .boolean y => decide (x ≠ y)
  | .literal .binary x,  .literal .binary y  => decide (x ≠ y)
  | .literal .null x,    .literal .null y    => decide (x ≠ y)
  -- `WFDouble`'s equality is a field of `numericHost`; see the docstring above
  | .literal .number _,   .literal .number _    => false
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

/-- Two literal payloads at one base that are different values. `OrthL` asks this of two terms;
    this asks it of the two payloads a pair of specs pins one name to.

    Four bases and not six, and the rows are the bases for the reason `OrthL` gives: a uniform
    row would be `noncomputable` at `number` and would stop `Orth` reducing at every pair.
    `null` has no row because two null literals carry the one inhabitant of `Unit`. -/
def altsDisj : Option Alts → Option Alts → Bool
  | some ⟨.string, x⟩,  some ⟨.string, y⟩  => decide (x ≠ y)
  | some ⟨.decimal, x⟩, some ⟨.decimal, y⟩ => decide (x ≠ y)
  | some ⟨.boolean, x⟩, some ⟨.boolean, y⟩ => decide (x ≠ y)
  | some ⟨.binary, x⟩,  some ⟨.binary, y⟩  => decide (x ≠ y)
  | _, _ => false

/-- One name that both specs declare, require, and pin to disjoint alternatives.

    Required presence on each side is a rule and not a precaution. Two objects sharing an
    *optional* literal name pinned to different values both admit the map that omits the name,
    so a req-blind test would certify a pair `select` cannot resolve. -/
def litDisjAt (sx sy : BodySpec) (k : Name) : Bool :=
  match sx.names.at k, sy.names.at k with
  | some nx, some ny =>
      decide (nx.presence = (true, false)) &&
      (decide (ny.presence = (true, false)) && altsDisj nx.alts ny.alts)
  | _, _ => false

/-- **Phase *literals*.** Two object options that pin one shared required name to different
    values.

    *The tag rule is about what a key can carry; the meet is about what a value can satisfy.*

    That sentence is the whole of why this is a phase of `Orth` and why it takes four bases
    where a tag takes two. A tag sits at `string` or `decimal` because a tag is read back as
    text. This asks only whether some value satisfies both structures, and a `boolean` or
    `binary` literal separates two objects as well as any.

    The existential is over the *first* spec's declared names, which is enough: a name the
    first spec does not declare pins nothing on the first side. -/
def OrthS (x y : Term) : Bool :=
  match specOf x, specOf y with
  | some sx, some sy => decide (∃ k : {k // k ∈ sx.names.1}, litDisjAt sx sy k.1 = true)
  | _, _ => false

/-- **The classifier.** A syntactic, decidable certificate that two terms cannot both admit
    one input — on both halves of the pair. `false` means "no certificate found". -/
def Orth (x y : Term) : Bool := Orth1 x y || OrthM x y || OrthS x y || OrthL x y

/-! ## Soundness

Two structural recursions, one per side, each mutual with a list companion for `union`. The
statement is about the **rows** (`Adm`/`AdmA`) and about `admitOptV`/`admitOptA`, never about
the term's own rows: `select` filters by the *option* semantics, and for an object option that is
structure — the names and the literal fields, not every field's contents — so a certificate
stated on `Adm` alone would not transfer.
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
theorem specOf_some_object {t : Term} {spec : BodySpec} (h : specOf t = some spec) :
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
    (hv : admitOptV (specOf t, Adm t) v = true) : occV t v.slot = true :=
  h v hv

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
  | .list _ _ _ =>
      fun v h => by cases v <;> simp_all [Adm, occV, occOnly, Value.slot]
  | .object (.mk _ _ _) => fun v h => by
      cases v <;> simp_all [Adm, AdmBody, occV, occOnly, Value.slot]
  | .held _ _ _ => fun _ _ => rfl
  | .refine t _ => fun v h => by
      simpa [occV] using occV_sound t v (Bool.and_eq_true_iff.mp h).1
  | .lazy t => fun v h => by simpa [occV] using occV_sound t v h
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
    (ha : admitOptA (specOf t, AdmA t) a = true) : occA t a.member = true :=
  h a ha

/-- A decimal literal reads only an `N`, and the row cannot be read off syntactically because
    it *asks its codec* — `AdmALit .decimal ls a = ((literalCodec .decimal ls).p a).isSome`.
    So the member comes from (W) on the read side instead: `Lawful.reads` says a
    member-naming codec accepts no other member, and `literalCodec_μ` names it. -/
theorem admALit_decimal_member {y : GroundKind.decimal.Carrier} {a : Attr}
    (h : AdmALit .decimal y a = true) : a.member = .N := by
  obtain ⟨v, hp⟩ := Option.isSome_iff_exists.mp (by simpa [AdmALit] using h)
  exact (lawful_literalCodec .decimal y).reads (literalCodec_μ .decimal y) hp

mutual

/-- **The read occupancy contains the row.** The mirror of `occV_sound`, with `held` and
    `literal .decimal` goes through (W) rather than through a pattern. -/
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
  | .list _ _ _ =>
      fun a h => by cases a <;> simp_all [AdmA, occA, occOnly, Attr.member]
  | .object (.mk _ _ _) => fun a h => by
      cases a <;> simp_all [AdmA, AdmABody, occA, occOnly, Attr.member]
  | .refine t _ => fun a h => by
      simpa [occA] using occA_sound t a (Bool.and_eq_true_iff.mp h).1
  | .held t _ _ => fun a h => by simpa [occA] using occA_sound t a h
  | .lazy t => fun a h => by simpa [occA] using occA_sound t a h
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

/-- **The name test really is disjointness of the admitted key sets.** `keysOk` puts the key
    set inside the presence each spec admits at the name. The two presences meet at the bottom,
    so the key set would have to lie inside the bottom, and no key set does: it either carries
    the name or omits it, and the meet refuses each answer.

    **No closedness premise, and none is needed.** An open body answers the top at an undeclared
    name, so no meet there is the bottom and an open body simply fails to separate on that name.
    An open body that *declares* a name at a refusing element still separates on the declared
    name, and this lemma covers that case with the rest. -/
theorem keysOk_of_presenceMeetsBot {sx sy : BodySpec} {k : Name}
    (h : presenceMeetsBot sx sy k = true)
    {keys : Finset Name} (hx : keysOk sx keys = true) (hy : keysOk sy keys = true) : False := by
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
  cases hk : decide (k ∈ keys) with
  | true =>
    have hm := of_decide_eq_true hk
    rw [presenceAt_fst_of_keysOk hx hm, presenceAt_fst_of_keysOk hy hm] at h1
    exact absurd h1 (by simp)
  | false =>
    have hm := of_decide_eq_false hk
    rw [presenceAt_snd_of_keysOk hx hm, presenceAt_snd_of_keysOk hy hm] at h2
    exact absurd h2 (by simp)

/-- …and from the separator, which is the same fact at whichever declared name meets. -/
theorem keysOk_of_namesSeparate {sx sy : BodySpec} (h : namesSeparate sx sy = true)
    {keys : Finset Name} (hx : keysOk sx keys = true) (hy : keysOk sy keys = true) : False := by
  rcases Bool.or_eq_true_iff.mp h with h' | h' <;>
    obtain ⟨k, hk⟩ := of_decide_eq_true h' <;>
    exact keysOk_of_presenceMeetsBot hk hx hy

theorem orthM_spec {x y : Term} (h : OrthM x y = true) :
    ∃ sx sy, specOf x = some sx ∧ specOf y = some sy ∧ namesSeparate sx sy = true := by
  unfold OrthM at h
  cases hsx : specOf x with
  | none => rw [hsx] at h; exact absurd h (by simp)
  | some sx =>
    cases hsy : specOf y with
    | none => rw [hsx, hsy] at h; exact absurd h (by simp)
    | some sy =>
      rw [hsx, hsy] at h
      exact ⟨sx, sy, rfl, rfl, h⟩

theorem orthSV_disjoint {x y : Term} (h : (Orth1 x y || OrthM x y) = true) :
    ∀ v, OrthSV x v → ¬ OrthSV y v := by
  rintro v ⟨hox, hax⟩ ⟨hoy, hay⟩
  rcases Bool.or_eq_true_iff.mp h with h1 | hm
  · exact occV_disjoint_of_Orth1 h1 hox hoy
  · obtain ⟨sx, sy, hsx, hsy, hr⟩ := orthM_spec hm
    obtain ⟨bx, rfl⟩ := specOf_some_object hsx
    obtain ⟨by', rfl⟩ := specOf_some_object hsy
    have hsxeq : bx.spec = sx := Option.some.inj hsx
    have hsyeq : by'.spec = sy := Option.some.inj hsy
    cases v with
    | map keys g =>
      have hkx : keysOk sx keys = true :=
        hsxeq ▸ (Bool.and_eq_true_iff.mp (structural_of_AdmBody hax)).1
      have hky : keysOk sy keys = true :=
        hsyeq ▸ (Bool.and_eq_true_iff.mp (structural_of_AdmBody hay)).1
      exact keysOk_of_namesSeparate hr hkx hky
    | _ => exact absurd hax (by cases bx; simp [admitOptV, Adm, AdmBody])

theorem orthSA_disjoint {x y : Term} (h : (Orth1 x y || OrthM x y) = true) :
    ∀ a, OrthSA x a → ¬ OrthSA y a := by
  rintro a ⟨hox, hax⟩ ⟨hoy, hay⟩
  rcases Bool.or_eq_true_iff.mp h with h1 | hm
  · exact occA_disjoint_of_Orth1 h1 hox hoy
  · obtain ⟨sx, sy, hsx, hsy, hr⟩ := orthM_spec hm
    obtain ⟨bx, rfl⟩ := specOf_some_object hsx
    obtain ⟨by', rfl⟩ := specOf_some_object hsy
    have hsxeq : bx.spec = sx := Option.some.inj hsx
    have hsyeq : by'.spec = sy := Option.some.inj hsy
    cases a with
    | m keys g =>
      have hkx : keysOk sx keys = true :=
        hsxeq ▸ (Bool.and_eq_true_iff.mp (structural_of_AdmABody hax)).1
      have hky : keysOk sy keys = true :=
        hsyeq ▸ (Bool.and_eq_true_iff.mp (structural_of_AdmABody hay)).1
      exact keysOk_of_namesSeparate hr hkx hky
    | _ => exact absurd hax (by cases bx; simp [admitOptA, AdmA, AdmABody])

/-- **What the discharger consumes.** Both families disjoint, as a `Prop` — the interface, of
    which `Orth` is the decidable part and the numeric base of phase *alternatives* the part
    that cannot be.

    Naming it is what keeps one discharger: a new phase is a new theorem producing
    `Separates`, not a new case in `uAtCan_of_separated`. -/
def Separates (x y : Term) : Prop :=
  (∀ v, OrthSV x v → ¬ OrthSV y v) ∧ (∀ a, OrthSA x a → ¬ OrthSA y a)

/-! ## Phase *alternatives*

Two literals at one base pinned to different values. The `Prop` below is uniform in the base and
`OrthL` decides it at four of the six, for the reason the file header gives. It is the
generalization of the hand instances at one base: `uAtCan_of_literalN_disjoint` in
`Discharge.lean` is one of them, and is now the caller that supplies the premise where `OrthL`
declines. Its siblings at the string base went with the per-aspect layer, this phase being
what reaches them. -/

/-- Different values make `inL` disjoint, at every base. Two bases are not the pattern match:

    * `null` — `inL .null _ .null` is `true` unconditionally, so two null literals are never
      disjoint. The premise is what rules it out, *vacuously*: `Unit` has exactly one
      inhabitant, so `x ≠ y` is uninhabited there. The rule needs no `k ≠ .null` side
      condition.
    * `decimal` — the comparison goes *through* the `Numeral.Stored` gate rather than round it,
      so the proof is a `split` on the `dite` rather than a rewrite. `by_cases` would reach
      `Classical.em`; `split` does not. -/
theorem inL_disjoint {k : GroundKind} {x y : k.Carrier}
    (hd : x ≠ y) (v : Value) (h : inL k x v = true) : inL k y v = false := by
  cases k with
  | string =>
    cases v with
    | str s =>
      replace h : decide (s = x) = true := h
      exact decide_eq_false (of_decide_eq_true h ▸ hd)
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
        exact decide_eq_false (h ▸ hd)
    | _ => rfl
  | boolean =>
    cases v with
    | bool b =>
      replace h : decide (b = x) = true := h
      exact decide_eq_false (of_decide_eq_true h ▸ hd)
    | _ => rfl
  | binary =>
    cases v with
    | bin b =>
      replace h : decide (b = x) = true := h
      exact decide_eq_false (of_decide_eq_true h ▸ hd)
    | _ => rfl
  | null =>
    cases v with
    | null => exact absurd (by cases x; cases y; rfl) hd
    | _ => rfl
  | decimal =>
    cases v with
    | str s =>
      show (if hst : Numeral.Stored s = true then
              decide ((⟨s, hst⟩ : StoredNumeral) = y) else false) = false
      replace h : (if hs : Numeral.Stored s = true then
              decide ((⟨s, hs⟩ : StoredNumeral) = x) else false) = true := h
      split
      · rename_i hst
        rw [dif_pos hst] at h
        exact decide_eq_false (of_decide_eq_true h ▸ hd)
      · rfl
    | _ => rfl

theorem denote_lit (k : GroundKind) (x : k.Carrier) :
    denote (.literal k x) = literalCodec k x := rfl

/-- The literal's read row *is* the codec's read domain — `AdmA_exact` with no hypothesis, so
    this is a rewrite rather than a discharge. It is what makes the read side of the rule
    uniform in the base: `AdmALit` is spelled per base (and at `decimal` it asks the codec),
    but the domain is `(baseCodec k).restrict (inL k ls)` at every base. -/
theorem admALit_iff {k : GroundKind} {x : k.Carrier} {a : Attr} :
    AdmALit k x a = true ↔ ((literalCodec k x).p a).isSome = true := by
  rw [← denote_lit k x, ← AdmA_literal k x a]
  exact AdmA_exact (.literal k x) a

/-- …and so the read side is the same `inL` disjointness, one level up: the base reads the
    attribute to *one* value, and one value cannot be in two disjoint held sets.

    This was the read-side argument the retired ~~SepA~~ instance made at a literal, and the
    reason §5 recorded the readable side as "undischargeable from the tables alone" was that
    the old `admALit .number` row was `⊤`. The row asks now, and this is where the argument
    lives. -/
theorem admALit_disjoint {k : GroundKind} {x y : k.Carrier}
    (hd : x ≠ y) (a : Attr)
    (h : AdmALit k x a = true) : AdmALit k y a = false := by
  obtain ⟨v, hp⟩ := Option.isSome_iff_exists.mp (admALit_iff.mp h)
  rw [literalCodec_p_restrict] at hp
  obtain ⟨hbase, hin⟩ := restrict_p.mp hp
  cases hq : AdmALit k y a with
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
theorem separates_literal_disjoint {k : GroundKind} {x y : k.Carrier}
    (hd : x ≠ y) :
    Separates (.literal k x) (.literal k y) := by
  refine ⟨?_, ?_⟩
  · rintro v ⟨-, hx⟩ ⟨-, hy⟩
    rw [specOf_none_admitOptV rfl, Adm_literal] at hx hy
    -- `AdmLit` is `inL`, full stop, since `number`'s `WF` conjunct became its carrier's
    have hix : inL k x v = true := hx
    have hiy : inL k y v = true := hy
    rw [inL_disjoint hd v hix] at hiy
    exact absurd hiy (by simp)
  · rintro a ⟨-, hx⟩ ⟨-, hy⟩
    rw [specOf_none_admitOptA rfl, AdmA_literal] at hx hy
    rw [admALit_disjoint hd a hx] at hy
    exact absurd hy (by simp)

/-! ### …and the same rule one spelling further out

`set` takes a base, so a set over a literal is a **restriction of the set**:
`refine(set b, each(members k x))`, and `setCodec_restrict` proves the two are one pair.
`sepJV_set_literals` is that separation at one pair of alternatives, on the write side.
These two are the rule, uniform in the base and on both halves. -/

/-- **A wire set cannot pass two disjoint held sets**, and `℘⁺fin` is the whole of it: the
    set has an element, and one element is not in both.

    The nonemptiness is what makes this a `set` fact rather than a container fact. An `array`
    admits `[]`, which passes every element predicate vacuously, and that is exactly why
    `not_uAtCan_array_literals` holds and `uAtAct_array_literals` is the most that pair
    meets. -/
theorem inLs_disjoint {k : GroundKind} {ls ls' : NEFinset k.Carrier}
    (hd : ∀ x ∈ ls.1, x ∉ ls'.1) (v : Value)
    (h : inLs k ls v = true) : inLs k ls' v = false := by
  obtain ⟨x, hx, hix⟩ := of_decide_eq_true h
  simp only [inLs, decide_eq_false_iff_not]
  rintro ⟨y, hy, hiy⟩
  rw [inL_disjoint (fun hxy => hd x hx (by rw [hxy]; exact hy)) v hix] at hiy
  exact absurd hiy (by simp)

/-- …and the set form one level out, where the wire set's elements are each asked. -/
theorem liftQ_inLs_disjoint {k : GroundKind} {ls ls' : NEFinset k.Carrier}
    (hd : ∀ x ∈ ls.1, x ∉ ls'.1) (v : Value)
    (h : liftQ (inLs k ls) v = true) : liftQ (inLs k ls') v = false := by
  cases v with
  | strSet S =>
      obtain ⟨z, hz⟩ := S.2
      simp only [liftQ, decide_eq_true_eq] at h
      simp only [liftQ, decide_eq_false_iff_not]
      exact fun hall => by
        have hne := inLs_disjoint hd (.str z) (h z hz)
        rw [hall z hz] at hne
        exact absurd hne (by simp)
  | numSet S =>
      obtain ⟨z, hz⟩ := S.2
      simp only [liftQ, decide_eq_true_eq] at h
      simp only [liftQ, decide_eq_false_iff_not]
      exact fun hall => by
        have hne := inLs_disjoint hd (.num z) (h z hz)
        rw [hall z hz] at hne
        exact absurd hne (by simp)
  | binSet S =>
      obtain ⟨z, hz⟩ := S.2
      simp only [liftQ, decide_eq_true_eq] at h
      simp only [liftQ, decide_eq_false_iff_not]
      exact fun hall => by
        have hne := inLs_disjoint hd (.bin z) (h z hz)
        rw [hall z hz] at hne
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
    have hlx : liftQ (inLs k ls) v = true := (Bool.and_eq_true_iff.mp hx).2
    have hly : liftQ (inLs k ls') v = true := (Bool.and_eq_true_iff.mp hy).2
    rw [liftQ_inLs_disjoint hd v hlx] at hly
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
        rw [liftQ_inLs_disjoint hd v hrx] at hry
        exact absurd hry (by simp)

/-- Phase *alternatives*, from its decidable half. One `split` over `OrthL`'s ten rows: five
    hand `separates_literal_disjoint` its premise, three hand `separates_setLiteral_disjoint`
    its premise and the base equality the read side needs, and two answer `false`. -/
theorem separates_of_orthL {x y : Term} (h : OrthL x y = true) : Separates x y := by
  unfold OrthL at h
  split at h
  · exact separates_literal_disjoint (of_decide_eq_true h)
  · exact separates_literal_disjoint (of_decide_eq_true h)
  · exact separates_literal_disjoint (of_decide_eq_true h)
  · exact separates_literal_disjoint (of_decide_eq_true h)
  · exact separates_literal_disjoint (of_decide_eq_true h)
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

/-! ## Phase *literals*

The name test reads the interval and this reads the contents, so the two are one `keysOk` and
one `literalsOk` apart. Both halves of the pair are the literal's own disjointness, reached
through the same two lemmas phase *alternatives* uses: `inL_disjoint` on the write side and
`admALit_disjoint` on the read side. -/

/-- Disjoint alternatives refute content admission on the write side: no value lies in both.

    Thirty-six rows and four of them do work — the diagonal at the four bases whose equality
    computes. `number` and `null` are off the diagonal here because `altsDisj` has no row for
    them, which is `OrthL`'s own concession arriving at the same two bases. -/
theorem altsDisj_disjointV {ax ay : Option Alts} (h : altsDisj ax ay = true) (v : Value)
    (hx : altsOkV ax v = true) (hy : altsOkV ay v = true) : False := by
  cases ax with
  | none => exact absurd h (by cases ay <;> simp [altsDisj])
  | some px =>
    cases ay with
    | none => obtain ⟨g, _⟩ := px; exact absurd h (by cases g <;> simp [altsDisj])
    | some py =>
      obtain ⟨gx, lx⟩ := px
      obtain ⟨gy, ly⟩ := py
      cases gx <;> cases gy <;>
        first
          | (have hx' : inL _ lx v = true := hx
             have hy' : inL _ ly v = true := hy
             rw [inL_disjoint (of_decide_eq_true h) v hx'] at hy'
             exact absurd hy' (by simp))
          | exact absurd h (by simp [altsDisj])

/-- …and on the read side, where the base reads the attribute to one value and one value
    cannot lie in two disjoint held sets. -/
theorem altsDisj_disjointA {ax ay : Option Alts} (h : altsDisj ax ay = true) (a : Attr)
    (hx : altsOkA ax a = true) (hy : altsOkA ay a = true) : False := by
  cases ax with
  | none => exact absurd h (by cases ay <;> simp [altsDisj])
  | some px =>
    cases ay with
    | none => obtain ⟨g, _⟩ := px; exact absurd h (by cases g <;> simp [altsDisj])
    | some py =>
      obtain ⟨gx, lx⟩ := px
      obtain ⟨gy, ly⟩ := py
      cases gx <;> cases gy <;>
        first
          | (have hx' : AdmALit _ lx a = true := admALit_iff.mpr hx
             have hy' : AdmALit _ ly a = true := admALit_iff.mpr hy
             rw [admALit_disjoint (of_decide_eq_true h) a hx'] at hy'
             exact absurd hy' (by simp))
          | exact absurd h (by simp [altsDisj])

/-- Structural admission at a required name: the name is present, and what it carries lies in
    the alternatives the spec pins it to. -/
theorem litOkV_of_admitOptV {sx : BodySpec} {keys : Finset Name}
    {f : {k // k ∈ keys} → Value} (h : (keysOk sx keys && literalsOk sx keys f) = true)
    {k : Name} (hk : k ∈ sx.names.1)
    (hreq : (sx.names.2 ⟨k, hk⟩).presence = (true, false)) :
    ∃ hm : k ∈ keys, litOkV sx k (f ⟨k, hm⟩) = true := by
  obtain ⟨hkeys, hlit⟩ := Bool.and_eq_true_iff.mp h
  have hm : k ∈ keys :=
    (of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hkeys).2).1) ⟨k, hk⟩
      (by simp [hreq])
  exact ⟨hm, (of_decide_eq_true hlit) ⟨k, hm⟩⟩

/-- …and its read-side twin, at the stored item. -/
theorem litOkA_of_admitOptA {sx : BodySpec} {keys : Finset Name}
    {g : {k // k ∈ keys} → Attr} (h : (keysOk sx keys && literalsOkA sx keys g) = true)
    {k : Name} (hk : k ∈ sx.names.1)
    (hreq : (sx.names.2 ⟨k, hk⟩).presence = (true, false)) :
    ∃ hm : k ∈ keys, litOkA sx k (g ⟨k, hm⟩) = true := by
  obtain ⟨hkeys, hlit⟩ := Bool.and_eq_true_iff.mp h
  have hm : k ∈ keys :=
    (of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hkeys).2).1) ⟨k, hk⟩
      (by simp [hreq])
  exact ⟨hm, (of_decide_eq_true hlit) ⟨k, hm⟩⟩

/-- **Phase *literals*, from its decidable half.** A phase producing `Separates`, so
    `uAtCan_of_separated` gains no case. -/
theorem separates_of_orthS {x y : Term} (h : OrthS x y = true) : Separates x y := by
  unfold OrthS at h
  cases hsx : specOf x with
  | none => rw [hsx] at h; exact absurd h (by simp)
  | some sx =>
    cases hsy : specOf y with
    | none => rw [hsx, hsy] at h; exact absurd h (by simp)
    | some sy =>
      rw [hsx, hsy] at h
      obtain ⟨k, hkd⟩ := of_decide_eq_true h
      cases hay : sy.names.at k.1 with
      | none =>
        rw [litDisjAt, hay] at hkd
        cases sx.names.at k.1 <;> exact absurd hkd (by simp)
      | some ny =>
        obtain ⟨hky, rfl⟩ := MapOf.at_eq_some.mp hay
        rw [litDisjAt, MapOf.at_of_mem k, MapOf.at_of_mem ⟨k.1, hky⟩] at hkd
        obtain ⟨hrxV, hrest⟩ := Bool.and_eq_true_iff.mp hkd
        obtain ⟨hryV, hda⟩ := Bool.and_eq_true_iff.mp hrest
        obtain ⟨bx, rfl⟩ := specOf_some_object hsx
        obtain ⟨by', rfl⟩ := specOf_some_object hsy
        have hsxeq : bx.spec = sx := Option.some.inj hsx
        have hsyeq : by'.spec = sy := Option.some.inj hsy
        refine ⟨?_, ?_⟩
        · rintro v ⟨-, hax⟩ ⟨-, hay'⟩
          cases v with
          | map keys f =>
            obtain ⟨hmx, hlx⟩ := litOkV_of_admitOptV (hsxeq ▸ structural_of_AdmBody hax) k.2
              (of_decide_eq_true hrxV)
            obtain ⟨hmy, hly⟩ := litOkV_of_admitOptV (hsyeq ▸ structural_of_AdmBody hay') hky
              (of_decide_eq_true hryV)
            rw [litOkV, MapOf.at_of_mem k] at hlx
            rw [litOkV, MapOf.at_of_mem ⟨k.1, hky⟩] at hly
            exact altsDisj_disjointV hda (f ⟨k.1, hmx⟩) hlx hly
          | _ => exact absurd hax (by cases bx; simp [admitOptV, Adm, AdmBody])
        · rintro a ⟨-, hax⟩ ⟨-, hay'⟩
          cases a with
          | m keys g =>
            obtain ⟨hmx, hlx⟩ := litOkA_of_admitOptA (hsxeq ▸ structural_of_AdmABody hax) k.2
              (of_decide_eq_true hrxV)
            obtain ⟨hmy, hly⟩ := litOkA_of_admitOptA (hsyeq ▸ structural_of_AdmABody hay') hky
              (of_decide_eq_true hryV)
            rw [litOkA, MapOf.at_of_mem k] at hlx
            rw [litOkA, MapOf.at_of_mem ⟨k.1, hky⟩] at hly
            exact altsDisj_disjointA hda (g ⟨k.1, hmx⟩) hlx hly
          | _ => exact absurd hax (by cases bx; simp [admitOptA, AdmA, AdmABody])

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
  rcases Bool.or_eq_true_iff.mp h with h'' | hl
  · rcases Bool.or_eq_true_iff.mp h'' with h' | hs
    · exact ⟨orthSV_disjoint h', orthSA_disjoint h'⟩
    · exact separates_of_orthS hs
  · exact separates_of_orthL hl

/-- **§5's (U), from pairwise separation.** The two other premises are the ones every
    discharger in `Discharge.lean` already takes: lawfulness, which soundness supplies, and
    the closed-object restriction.

    `hblk` asks that an open block's term denotes a lawful codec. The premise was
    `Term.isOpenObject = false`, which refused the open object outright. The structural
    lemmas now read the block, so an open option admits through a union like any other, and
    the residue is lawfulness alone: `optionSem_self_admit` reads the block's codec back and
    needs that codec to retract. A closed body discharges `hblk` with no content. -/
theorem uAtCan_of_separated {opts : List Term}
    (hlaw : ∀ t ∈ opts, Lawful (denote t))
    (hblk : ∀ t ∈ opts, ∀ fields ff wild, t = .object (.mk fields ff wild) →
      ∀ w : KeyPat × Term, wild = some w → Lawful (denote w.2))
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
    exact optionSem_self_admit t (hblk t ht) (hlaw t ht) he

/-- **Pairwise separation is the structural certificate**, which is (U)'s premise read as a
    counting fact rather than as a singleton one.

    `UniqueBothWays` asks that a filter *is* `[o]`; `AdmitsAtMostOne` asks only that no filter is
    longer than one. The second is what `uAtAct_sublist` needs, because it is monotone under a
    sub-selection where the first is not. Every phase supplies it at once: separation says no two
    options admit one input, and admission implies occupancy through `occV_sound`, so the two
    conjuncts of `OrthSV` are both in hand.

    Stated on `Separated` and not on `OrthS`, because the argument reads none of the phases. -/
theorem admitsAtMostOne_of_separated {opts : List Term} (h : Separated opts) :
    AdmitsAtMostOne (semsOf opts) := by
  constructor
  · intro v
    rw [show semsOf opts = optionSems opts from (optionSems_eq opts).symm,
      filter_AdmSpecs (fun t _ => Adm_exact t) v, List.length_map]
    refine length_le_one_of_pairwise_false (List.Pairwise.imp_of_mem ?_
      (List.Pairwise.filter _ (h.imp fun hs => hs.1 v)))
    intro x y hx hy hxy
    have hax : admitOptV (specOf x, Adm x) v = true := (List.mem_filter.mp hx).2
    have hay : admitOptV (specOf y, Adm y) v = true := (List.mem_filter.mp hy).2
    exact hxy ⟨occV_admitOpt (occV_sound x) v hax, hax⟩
      ⟨occV_admitOpt (occV_sound y) v hay, hay⟩
  · intro a
    rw [show semsOf opts = optionSems opts from (optionSems_eq opts).symm,
      filter_AdmASpecs (fun t _ => AdmA_exact t) a, List.length_map]
    refine length_le_one_of_pairwise_false (List.Pairwise.imp_of_mem ?_
      (List.Pairwise.filter _ (h.imp fun hs => hs.2 a)))
    intro x y hx hy hxy
    have hax : admitOptA (specOf x, AdmA x) a = true := (List.mem_filter.mp hx).2
    have hay : admitOptA (specOf y, AdmA y) a = true := (List.mem_filter.mp hy).2
    exact hxy ⟨occA_admitOpt (occA_sound x) a hax, hax⟩
      ⟨occA_admitOpt (occA_sound y) a hay, hay⟩

/-- The classifier's answer for a whole option list, which is the one bridge from the decidable
    phase to the `Prop` the discharger takes. -/
theorem separated_of_orth {opts : List Term}
    (h : List.Pairwise (fun x y => Orth x y = true) opts) : Separated opts :=
  h.imp separates_of_orth

/-- …and from the decidable classifier, which is the form `uAtAct_sublist` takes at a call site. -/
theorem admitsAtMostOne_of_orth {opts : List Term}
    (h : List.Pairwise (fun x y => Orth x y = true) opts) :
    AdmitsAtMostOne (semsOf opts) :=
  admitsAtMostOne_of_separated (separated_of_orth h)

/-- …and from the decidable premise alone, which reaches six of the twenty-five hand
    discharges; seven more need `Separates` and `uAtCan_of_separated` above, for thirteen of
    twenty-five between them. The by-phase table at the end of the file is the measurement. -/
theorem uAtCan_of_orth {opts : List Term}
    (hlaw : ∀ t ∈ opts, Lawful (denote t))
    (hblk : ∀ t ∈ opts, ∀ fields ff wild, t = .object (.mk fields ff wild) →
      ∀ w : KeyPat × Term, wild = some w → Lawful (denote w.2))
    (h : List.Pairwise (fun x y => Orth x y = true) opts) :
    UAtCan opts :=
  uAtCan_of_separated hlaw hblk (separated_of_orth h)

/-- …and the residue the laws actually need. -/
theorem uAtAct_of_orth {opts : List Term}
    (hlaw : ∀ t ∈ opts, Lawful (denote t))
    (hblk : ∀ t ∈ opts, ∀ fields ff wild, t = .object (.mk fields ff wild) →
      ∀ w : KeyPat × Term, wild = some w → Lawful (denote w.2))
    (h : List.Pairwise (fun x y => Orth x y = true) opts) :
    UAtAct opts :=
  uAtAct_of_uAtCan (uAtCan_of_orth hlaw hblk h)

/-! ## The same certificate, on the held sets

`separates_of_orth` above is stated on `Adm`, which is what an option **writes**. §5's (D) is
stated on held sets, and the two are not the same set: `T = dom(e)` fails at a `union` whose
options both admit one value, where `select` writes nothing and the held set keeps it
(`TIsDomE`, `not_TIsDomE_unionLiteralString`). So disjoint admission does not give disjoint
held sets, and `Typed.union`'s (D) cannot be discharged through `separates_of_orth`.

The mirror below re-runs each phase against the judgement instead. It needs the value half
only, because a held set is a set of values. `uAtCan_of_orth` takes a closedness premise
for a different reason, which is admission and not separation: an open option's admission is
not structural, so `optionSem_self_admit` needs it where this phase no longer does. -/

/-- The option list's held occupancy, for the `union` row below. -/
theorem typed_occVL : ∀ {opts : List Term} {Ts μs}, TypedListμ opts Ts μs →
    (∀ t ∈ opts, ∀ (T : Held) (μ), Typed t T μ → ∀ v, T v → occV t v.slot = true) →
    ∀ (v : Value) (T : Held), T ∈ Ts → T v → occVL opts v.slot = true
  | _, _, _, .nil, _, _, _, hT, _ => nomatch hT
  | _, _, _, .cons hty hs, ih, v, T, hT, hv => by
    rcases List.mem_cons.mp hT with rfl | hT'
    · simp only [occVL, Bool.or_eq_true]
      exact Or.inl (ih _ List.mem_cons_self _ _ hty v hv)
    · simp only [occVL, Bool.or_eq_true]
      exact Or.inr (typed_occVL hs (fun x hx => ih x (List.mem_cons_of_mem _ hx)) v T hT' hv)

set_option linter.unreachableTactic false in
/-- **Every held value's slot is one the term occupies**, which is `occV_sound` against the
    judgement rather than against `Adm`. The `⊤` rows cost nothing, and a set whose kind does
    not match its base is empty, which its carrier forbids. -/
theorem typed_occV : ∀ {t T μ}, Typed t T μ → ∀ v, T v → occV t v.slot = true
  | t, T, μ, h, v, hv => by
    cases h with
    | string => obtain ⟨s, rfl⟩ := hv; rfl
    | number => obtain ⟨d, rfl, _⟩ := hv; rfl
    | decimal => obtain ⟨s, rfl, _⟩ := hv; rfl
    | boolean => obtain ⟨b, rfl⟩ := hv; rfl
    | null => subst hv; rfl
    | binary => obtain ⟨b, rfl⟩ := hv; rfl
    | literal k x => subst hv; cases k <;> rfl
    | never => exact absurd hv (hnever_false v)
    | set b =>
        rcases hv with ⟨S, rfl, hall⟩ | ⟨S, rfl, hall⟩ | ⟨S, rfl, hall⟩ <;>
          cases b <;>
          simp_all [occV, occOnly, Value.slot, SetBase.slot, SetBase.held] <;>
          exact S.2.elim (fun a ha => hall a ha)
    | list _ _ _ => obtain ⟨vs, rfl, _⟩ := hv; rfl
    | object _ _ => obtain ⟨keys, f, rfl, _⟩ := hv; rfl
    | held _ => rfl
    | @refine t' T' μ' q h' => exact typed_occV h' v hv.1
    | @lazy t' T' μ' h' => exact typed_occV h' v hv
    | opaq lossy =>
        cases lossy with
        | true => rfl
        | false => cases hv <;> simp_all [occV, occBut, Value.slot]
    | @union opts Ts μs h' _ =>
        obtain ⟨T', hT', hv'⟩ := hv
        exact typed_occVL h' (fun t' _ _ _ hty w hw => typed_occV hty w hw) v T' hT' hv'
termination_by t _ _ _ _ => Term.depth t
decreasing_by term_depth_wf

/-- **Phase *slot*, on the held sets.** -/
theorem held_disj_of_Orth1 {x y : Term} {Tx Ty : Held} {μx μy : Option Member}
    (h : Orth1 x y = true) (hx : Typed x Tx μx) (hy : Typed y Ty μy) : HDisj Tx Ty :=
  fun v hvx hvy => occV_disjoint_of_Orth1 h (typed_occV hx v hvx) (typed_occV hy v hvy)

set_option linter.unnecessarySimpa false in
/-- **Phase *alternatives*, on the held sets.** Two literals pinned to different values hold
    different values, and two restricted sets with no common alternative hold no common set:
    a set value held by both would have every element in both alternative sets, and its
    carrier gives it an element. -/
theorem held_disj_of_OrthL {x y : Term} {Tx Ty : Held} {μx μy : Option Member}
    (h : OrthL x y = true) (hx : Typed x Tx μx) (hy : Typed y Ty μy) : HDisj Tx Ty := by
  unfold OrthL at h
  split at h
  case _ a b | _ a b | _ a b | _ a b | _ a b =>
    cases hx; cases hy
    intro v hvx hvy
    simp only [HLit] at hvx hvy
    subst hvx
    simp only [GroundKind.toValue] at hvy
    have hne := of_decide_eq_true h
    first
      | exact hne (by simpa using hvy)
      | exact hne (Subtype.ext (by simpa using hvy))
  case _ => exact absurd h (by simp)
  case _ b ls b' ls' | _ b ls b' ls' | _ b ls b' ls' =>
    obtain ⟨hb, hd⟩ := Bool.and_eq_true_iff.mp h
    cases hx
    rename_i hx'
    cases hx'
    cases hy
    rename_i hy'
    cases hy'
    intro v hvx hvy
    have hq1 := hvx.2
    have hq2 := hvy.2
    simp only [Pred.eval] at hq1 hq2
    cases v
    case strSet S =>
      exact S.2.elim (fun s hs => by
        simp_all [liftQ, inLs, inL, disjAlts]
        all_goals
          obtain ⟨p1, hm1⟩ := hq1 s hs
          obtain ⟨p2, hm2⟩ := hq2 s hs
          exact h _ p1 hm1 hm2)
    case numSet S => exact S.2.elim (fun d hd => by simp_all [liftQ, inLs, inL, disjAlts])
    case binSet S => exact S.2.elim (fun w hw => by simp_all [liftQ, inLs, inL, disjAlts])
    all_goals simp_all [liftQ]
  case _ => exact absurd h (by simp)

/-- A term with a name spec is an object, and the spec is that object's body's. -/
theorem specOf_object {t : Term} {s : BodySpec} (h : specOf t = some s) :
    ∃ b : Body, t = .object b ∧ s = b.spec := by
  cases t <;> simp only [specOf, reduceCtorEq] at h
  exact ⟨_, rfl, (Option.some.inj h).symm⟩

/-- A body with no open block holds nothing there: the open part of the held set is absent. -/
theorem typedWild_none {w : Option (KeyPat × Term)} {R : Option Held} (h : TypedWild w R)
    (ho : w.isSome = false) : R = none := by
  cases h <;> simp_all

/-- A body's spec is indexed by that body's own names. -/
@[simp] theorem Body.spec_keys (b : Body) : b.spec.names.keys = b.fields := by cases b; rfl

/-- The spec's write presence reads off the slot at the same name. -/
theorem body_spec_presence {b : Body} (k : {k // k ∈ b.spec.names.keys}) (hk : k.1 ∈ b.fields) :
    (b.spec.names.get k).presence = (b.at ⟨k.1, hk⟩).presence := by
  cases b; rfl

/-- A write-required name is a name whose field is not `optional`, which is the
    premise `TypedField.true_of_not_optional` takes. -/
theorem body_spec_requiredV {b : Body} (k : {k // k ∈ b.spec.names.keys})
    (h : (b.spec.names.get k).presence = (true, false)) (hk : k.1 ∈ b.fields) :
    ∀ t', b.at ⟨k.1, hk⟩ ≠ .optional t' := by
  intro t' hc
  rw [body_spec_presence k hk, hc] at h
  cases t' <;> simp [ObjectSlot.presence, Term.isNever] at h

/-- **A body's held set puts its key set inside the presence its spec admits.** The present
    half: a name whose element refuses absence is in the key set of every map the body holds.
    `HObject`'s required-name conjunct, read through the slot. -/
theorem held_presence_fst {b : Body} {T : Held} {μ : Option Member}
    (ht : Typed (.object b) T μ) {v : Value} (hv : T v)
    {keys : Finset Name} {f} (hveq : v = .map keys f) {k : Name}
    (hk : k ∉ keys) : (b.spec.presenceAt k).2 = true := by
  cases ht with
  | @object _ bind R μs hf hr =>
    obtain ⟨keys', f', heq, hpres, _⟩ := hv
    rw [hveq] at heq
    cases heq
    unfold BodySpec.presenceAt
    cases hat : b.spec.names.at k with
    | some ns =>
      obtain ⟨hd, rfl⟩ := MapOf.at_eq_some.mp hat
      have hkm : k ∈ b.fields := by rw [← Body.spec_keys]; exact hd
      cases hp : (b.spec.names.get ⟨k, hd⟩).presence.2 with
      | true => rfl
      | false =>
        refine absurd (hpres ⟨k, hkm⟩
          (TypedField.true_of_not_optional (hf ⟨k, hkm⟩) (fun t' hc => ?_))) hk
        -- the slot admits no absence, so the slot is not `optional`
        rw [body_spec_presence ⟨k, hd⟩ hkm, hc] at hp
        cases t' <;> simp [ObjectSlot.presence, Term.isNever] at hp
    | none => cases b.spec.wild.isSome <;> rfl

/-- …and the absent half: a name whose element refuses presence is out of the key set of every
    map the body holds. An undeclared name falls to the open block, and a body with no block
    holds nothing there. -/
theorem held_presence_snd {b : Body} {T : Held} {μ : Option Member}
    (ht : Typed (.object b) T μ) {v : Value} (hv : T v)
    {keys : Finset Name} {f} (hveq : v = .map keys f) {k : Name}
    (hk : k ∈ keys) : (b.spec.presenceAt k).1 = true := by
  cases ht with
  | @object _ bind R μs hf hr =>
    obtain ⟨keys', f', heq, _, hent⟩ := hv
    rw [hveq] at heq
    cases heq
    unfold BodySpec.presenceAt
    cases hat : b.spec.names.at k with
    | some ns =>
      obtain ⟨hd, rfl⟩ := MapOf.at_eq_some.mp hat
      have hkm : k ∈ b.fields := by rw [← Body.spec_keys]; exact hd
      have he := hent ⟨k, hk⟩
      rw [dif_pos hkm] at he
      cases hp : (b.spec.names.get ⟨k, hd⟩).presence.1 with
      | true => rfl
      | false =>
        -- the element refuses presence, so the slot's term is `never` and its held set is empty
        exfalso
        rw [body_spec_presence ⟨k, hd⟩ hkm] at hp
        -- the slot's term is `never` on either mark, so the field's held set is `HNever`
        obtain ⟨t', hty, hshape⟩ := TypedField.term (hf ⟨k, hkm⟩)
        have hnv : t' = .never := by
          rcases hshape with hs | hs <;> rw [hs] at hp <;>
            cases t' <;> simp [ObjectSlot.presence, ObjectSlot.isReq, Term.isNever] at hp ⊢
        cases hnv
        -- `Typed .never` has one constructor and it pins the held set to `HNever`, which is
        -- empty. The projection is generalized first, so the elimination has a variable motive.
        generalize hgT : (bind ⟨k, hkm⟩).2 = T' at he hty
        generalize (μs ⟨k, hkm⟩) = m at hty
        cases hty
        exact (hnever_false _) he
    | none =>
      have hnd : k ∉ b.fields := by
        intro hm
        rw [MapOf.at_of_mem (m := b.spec.names) ⟨k, by rw [Body.spec_keys]; exact hm⟩] at hat
        exact nomatch hat
      have he := hent ⟨k, hk⟩
      rw [dif_neg hnd] at he
      obtain ⟨T', hT', _⟩ := he
      cases hw : b.wild.isSome with
      | true =>
        have : b.spec.wild.isSome = true := by
          have hb := Body.spec_wild_isNone b
          cases hwb : b.spec.wild <;> cases hwb2 : b.wild <;>
            simp_all [Option.isNone, Option.isSome]
        rw [this]; rfl
      | false => rw [typedWild_none hr hw] at hT'; exact nomatch hT'

/-- **Phase *names*, one direction, on the held sets.** The two bodies admit presences at one
    name that meet at the bottom, and each body's held set puts its key set inside the presence
    it admits. So no map lies in both held sets. -/
theorem held_disj_of_presenceMeetsBot {a b : Body} {Ta Tb : Held} {μa μb : Option Member}
    {k : Name} (h : presenceMeetsBot a.spec b.spec k = true)
    (hta : Typed (.object a) Ta μa) (htb : Typed (.object b) Tb μb) : HDisj Ta Tb := by
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
  intro v hva hvb
  -- both held sets are objects, so the value is a map
  have hm : ∃ keys f, v = .map keys f := by
    cases hta with
    | @object _ bind R μs hf hr => obtain ⟨keys, f, rfl, _, _⟩ := hva; exact ⟨keys, f, rfl⟩
  obtain ⟨keys, f, rfl⟩ := hm
  cases hk : decide (k ∈ keys) with
  | true =>
    have hmem := of_decide_eq_true hk
    rw [held_presence_snd hta hva rfl hmem, held_presence_snd htb hvb rfl hmem] at h1
    exact absurd h1 (by simp)
  | false =>
    have hmem := of_decide_eq_false hk
    rw [held_presence_fst hta hva rfl hmem, held_presence_fst htb hvb rfl hmem] at h2
    exact absurd h2 (by simp)

/-- The mirror of `HDisj`'s own symmetry, used to read the second direction off the first. -/
theorem HDisj.symm {Tx Ty : Held} (h : HDisj Tx Ty) : HDisj Ty Tx :=
  fun v hy hx => h v hx hy

/-- **Phase *names*, on the held sets.**

    **No closedness premise, and that is the phase becoming sound rather than a premise being
    dropped.** `OrthM` refuses a body with an open block, so a pair it certifies is a pair of
    closed bodies and the judgement side needs no separate guarantee. While the phase read the
    field table alone it certified a closed object against an open one that holds the very map
    the closed one requires, and the premise was the only thing standing in front of it. -/
theorem held_disj_of_OrthM {x y : Term} {Tx Ty : Held} {μx μy : Option Member}
    (h : OrthM x y = true)
    (hx : Typed x Tx μx) (hy : Typed y Ty μy) : HDisj Tx Ty := by
  obtain ⟨sx, sy, hsx, hsy, hr⟩ := orthM_spec h
  obtain ⟨bx, rfl, rfl⟩ := specOf_object hsx
  obtain ⟨by_, rfl, rfl⟩ := specOf_object hsy
  rcases Bool.or_eq_true_iff.mp hr with h' | h' <;>
    obtain ⟨k, hk⟩ := of_decide_eq_true h' <;>
    exact held_disj_of_presenceMeetsBot hk hx hy

/-- What the spec pins at a declared name, it reads off that name's field. -/
theorem body_spec_alts {b : Body} (k : {k // k ∈ b.spec.names.keys}) (hk : k.1 ∈ b.fields) :
    (b.spec.names.get k).alts = altsOfField (b.at ⟨k.1, hk⟩) := by
  cases b; rfl

/-- A field the spec pins to a literal holds that literal's value and no other. Every field
    form, because `altsOfField` reads all three: a present name is pinned whether or not the
    field is required. -/
theorem held_lit_of_alts {fd : ObjectSlot} {T : Held} {π μ} {kd : GroundKind} {a : kd.Carrier}
    (halts : altsOfField fd = some ⟨kd, a⟩) (h : TypedField fd T π μ) :
    ∀ v, T v → v = kd.toValue a := by
  obtain ⟨t', hty, hshape⟩ := TypedField.term h
  rcases hshape with ⟨m, rfl⟩ | rfl <;>
    cases t' <;> simp only [altsOfField, reduceCtorEq] at halts <;>
    cases halts <;> cases hty <;> exact fun v hv => hv

set_option linter.unnecessarySimpa false in
/-- **Phase *literals*, on the held sets.** Both specs require the shared name, so every map
    either holds carries it, and each side pins its value to a different literal. -/
theorem held_disj_of_OrthS {x y : Term} {Tx Ty : Held} {μx μy : Option Member}
    (h : OrthS x y = true) (hx : Typed x Tx μx) (hy : Typed y Ty μy) : HDisj Tx Ty := by
  unfold OrthS at h
  cases hsx : specOf x with
  | none => rw [hsx] at h; exact absurd h (by simp)
  | some sx =>
    cases hsy : specOf y with
    | none => rw [hsx, hsy] at h; exact absurd h (by simp)
    | some sy =>
      rw [hsx, hsy] at h
      obtain ⟨bx, rfl, rfl⟩ := specOf_object hsx
      obtain ⟨b2, rfl, rfl⟩ := specOf_object hsy
      obtain ⟨k, hlit⟩ := of_decide_eq_true h
      have hkx : k.1 ∈ bx.fields := by rw [← Body.spec_keys]; exact k.2
      unfold litDisjAt at hlit
      rw [show bx.spec.names.at k.1 = some (bx.spec.names.get k) by
            simp only [MapOf.at, dif_pos k.2]] at hlit
      cases hay : b2.spec.names.at k.1 with
      | none => rw [hay] at hlit; exact absurd hlit (by simp)
      | some ny =>
        rw [hay] at hlit
        obtain ⟨hky, rfl⟩ := MapOf.at_eq_some.mp hay
        obtain ⟨hreqxV, hrest⟩ := Bool.and_eq_true_iff.mp hlit
        obtain ⟨_, hd⟩ := Bool.and_eq_true_iff.mp hrest
        have hky' : k.1 ∈ b2.fields := by rw [← Body.spec_keys]; exact hky
        rw [body_spec_alts k hkx, body_spec_alts ⟨k.1, hky⟩ hky'] at hd
        cases hx with
        | @object _ bindx Rx μsx hfx hrx =>
          cases hy with
          | @object _ bindy Ry μsy hfy hry =>
            intro v hvx hvy
            obtain ⟨keys, f, rfl, hpresx, hentx⟩ := hvx
            obtain ⟨keys', f', heq, hpresy, henty⟩ := hvy
            cases heq
            have hin : k.1 ∈ keys :=
              hpresx ⟨k.1, hkx⟩
                (TypedField.true_of_not_optional (hfx ⟨k.1, hkx⟩)
                  (body_spec_requiredV k (of_decide_eq_true hreqxV) hkx))
            have hex := hentx ⟨k.1, hin⟩
            have hey := henty ⟨k.1, hin⟩
            rw [dif_pos hkx] at hex
            rw [dif_pos hky'] at hey
            unfold altsDisj at hd
            split at hd
            case _ ax ay | _ ax ay | _ ax ay | _ ax ay =>
              have h1 := held_lit_of_alts (by assumption) (hfx ⟨k.1, hkx⟩) _ hex
              have h2 := held_lit_of_alts (by assumption) (hfy ⟨k.1, hky'⟩) _ hey
              rw [h1] at h2
              have hne := of_decide_eq_true hd
              simp only [GroundKind.toValue] at h2
              first
                | exact hne (by simpa using h2.symm)
                | exact hne (by simpa using h2)
                | exact hne (Subtype.ext (by simpa using h2.symm))
                | exact hne (Subtype.ext (by simpa using h2))
            case _ => exact absurd hd (by simp)

/-- **The certificate separates held sets.** Whichever phase found the certificate, two
    derivable closed options hold no value in common. This is what `Typed.union`'s (D) takes,
    in the disjointness form `dincomp_of_disjoint` reads. -/
theorem separates_held_of_orth {x y : Term} {Tx Ty : Held} {μx μy : Option Member}
    (h : Orth x y = true)
    (hx : Typed x Tx μx) (hy : Typed y Ty μy) : HDisj Tx Ty := by
  rcases Bool.or_eq_true_iff.mp h with h'' | hl
  · rcases Bool.or_eq_true_iff.mp h'' with h' | hs
    · rcases Bool.or_eq_true_iff.mp h' with h1 | hm
      · exact held_disj_of_Orth1 h1 hx hy
      · exact held_disj_of_OrthM hm hx hy
    · exact held_disj_of_OrthS hs hx hy
  · exact held_disj_of_OrthL hl hx hy

/-! ## The classifier, checked against the table

`Orth` is decidable, so the checks below are `by decide` rather than proofs — which is the
point of having it. The negatives matter more than the positives: **the ten `not_sep*`
witnesses are a ready-made unsoundness test suite**, and if `Orth` certified one of them
`Orth` would be wrong. It certifies none. -/

private def lsA : String := "A"
private def lsB : String := "B"

/-- …and the set forms, for `Pred.members`, which keeps its `Finset` where a literal lost one. -/
private def setA : NEFinset String := ⟨{"A"}, Finset.singleton_nonempty _⟩
private def setB : NEFinset String := ⟨{"B"}, Finset.singleton_nonempty _⟩

theorem orth_string_number : Orth .string .number = true := by decide
theorem orth_string_null : Orth .string .null = true := by decide
theorem orth_string_boolean : Orth .string .boolean = true := by decide
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
    Orth (.object (.mk {"petId", "price"} (fun _ => .req .string) none))
         (.object (.mk {"petIds"} (fun _ => .req .string) none)) = true := by decide

/-- …and the ambiguity §5 names: **an optional binding widens admission**, so two objects
    declaring only optional names both admit the empty map and are not separated however
    disjoint their names are. -/
theorem orth_objects_optional_only :
    Orth (.object (.mk {"a"} (fun _ => .optional .string) none))
         (.object (.mk {"b"} (fun _ => .optional .string) none)) = false := by decide

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
  simp [Orth, Orth1, OrthM, OrthS, OrthL, occV, occA, occTop, occOnly, Slot.all, Member.all, specOf]

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
theorem not_orth_literal_number (x y : GroundKind.number.Carrier) :
    Orth (.literal .number x) (.literal .number y) = false := by
  simp [Orth, Orth1, OrthM, OrthS, OrthL, occV, occA, occOnly, Slot.all, Member.all, specOf,
    GroundKind.slot, GroundKind.member]

/-- **Two null literals are never disjoint**, and `false` here is exact rather than a
    concession: `NEFinset Unit` has one inhabitant, so both hold `()`. -/
theorem not_orth_literal_null (x y : GroundKind.null.Carrier) :
    Orth (.literal .null x) (.literal .null y) = false := by
  simp [Orth, Orth1, OrthM, OrthS, OrthL, occV, occA, occOnly, Slot.all, Member.all, specOf,
    GroundKind.slot, GroundKind.member]

/-- **The same rule at a set**, which is the pair `Separation.lean` discharges by hand as
    `sepJV_set_literals` — and only on the write side, `SepJV` being about `Adm`. The
    certificate answers both halves. `℘⁺fin` is what makes it a `set` fact: the payload has an
    element, and one element is not in two disjoint held sets. -/
theorem orth_set_literals :
    Orth (.refine (.set .string) (.each (.members .string setA)))
         (.refine (.set .string) (.each (.members .string setB))) = true := by decide

/-- …and not where the alternatives meet. -/
theorem not_orth_set_literals_same :
    Orth (.refine (.set .string) (.each (.members .string setA)))
         (.refine (.set .string) (.each (.members .string setA))) = false := by decide

/-- **Two set bases decline**, and the read side is the reason: `refineReads` has the base
    decode the attribute, so two bases decode one attribute to two values and there is
    nothing to compare. `set(string)` and `set(decimal)` are the pair that shows it, both
    writing a `strSet` while storing `SS` and `NS`. -/
theorem not_orth_set_literals_two_bases :
    Orth (.refine (.set .string) (.each (.members .string setA)))
         (.refine (.set .decimal) (.each (.members .string setB))) = false := by decide

/-- **A `closure` beside a `members` is not certified**, which is the case `Pred` keeps rather
    than removes. Holds for every `q`, so this is phase *opaque predicate* and not a gap. -/
theorem not_orth_set_literal_closure (q : Value → Bool) :
    Orth (.refine (.set .string) (.each (.members .string setA)))
         (.refine (.set .string) (.each (.closure q))) = false := by
  simp [Orth, Orth1, OrthM, OrthS, OrthL, occV, occA, occOnly, Slot.all, Member.all, specOf,
    SetBase.slot, SetBase.member]

/-- …and the pair, discharged from one `decide` where it used to name its premise. At
    `.number` the route is still `separates_literal_disjoint` with the premise proved by
    hand, `DecidableEq Double` being noncomputable; that is `uAtCan_of_literalN_disjoint`'s
    content, generalized. -/
theorem uAtCan_literal_literal_by_orth :
    UAtCan [Term.literal .string lsA, Term.literal .string lsB] :=
  uAtCan_of_orth (forall_mem_pair (lawful_literal _ _) (lawful_literal _ _))
    (forall_mem_pair (fun _ _ _ h => nomatch h) (fun _ _ _ h => nomatch h))
    (List.pairwise_pair.mpr (by decide))

/-! ### The existing discharges, by phase

Where the hand proofs sit, and the two that sit nowhere. `Orth` is the decidable part, and
`Separates` covers what is left of phase *alternatives*; the last column says which.

| theorem | phase | reached |
| --- | --- | --- |
| `uAtCan_of_literalN_disjoint` | alternatives | `separates_literal_disjoint`, the base `OrthL` declines |
| `uAtCan_of_refine_disjoint`, `uAtCan_boolLiterals`, `uAtCan_refine_container` | opaque predicate | never — `q` is arbitrary |
| `sepJV_set_literals` | alternatives | `OrthL`'s set rows, and on both halves where the hand proof is `SepJV` |
| ~~uAtCan_dunion~~ | tag | the constructor is gone: a dissection is a certified `union`, and phase *literals* certifies it |
| `uAtCan_opaque` | kind | one level below the term language |
| `uAtAct_array_literals` | none: `UAtCan` itself is false | never — there is nothing to certify |

**The rows that are gone were the reason this table was worth having.** Every discharge in
phase *slot*, and the string-base half of phase *alternatives*, was a hand proof stated on the
per-aspect ~~SepV~~/~~SepA~~ and reached here by `decide` — so when that layer was retired the
hand proofs went with it and this file is what certifies those pairs now. Three more went with
the four tables: ~~sep_lazy_literal~~, ~~sepA_lazy_literal~~ and ~~sep_nullable_plain~~ were
stated on the retired rows, and each said that a transparent wrapper over a literal separates
from a plain literal exactly as the subterm does. Nothing consumed them, and `Adm` and `AdmA`
pass through `lazy` by definition, so the fact is the rows' rather than a theorem's. What is left is the two phases `Orth` does *not* reach, the numeric base of
phase *alternatives*, and the two constructors below the term language: the table has stopped
being a map of duplicated work and is now a list of what only exists by hand.

**Two fit no phase of the classifier, and each is a limit worth naming** — a different limit
from the row above them, where the phase is `none` because `UAtCan` is false and there is no
orthogonality to certify at all.

`LegacyRead` stays outside `Term`. `legacyRead_reads_n` shows an alternate reader can read a numeric attribute through a string core. `Orth` classifies current terms only.

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
    (forall_mem_pair (fun _ _ _ h => nomatch h) (fun _ _ _ h => nomatch h))
    (List.pairwise_pair.mpr (by decide))

end Calculus
