import Calculus.ExactA

/-!
# Orthogonality — a decidable certificate of separation

`Obligations (.union opts)` carries pairwise compatibility. Two orthogonal options are
compatible (`pairwiseCompat_of_orth`).

`Orth` is that rule, written once. It is a **phase classifier**: given a pair of terms it
answers whether there is a *syntactic certificate* that they cannot both admit one input.

## Sound, never complete, and why there is no `unknown`

Semantic orthogonality is undecidable in this language — `refine t q` carries an arbitrary
`Value → Bool` and `held t P f g` an arbitrary pair of maps. So `Orth` answers a *narrower* question, and the answer `false` means "no
certificate", never "not orthogonal".

The direction that keeps this sound is that **over-approximating an occupancy is always
safe**: if `X ⊆ X'`, `Y ⊆ Y'` and `X' ∩ Y' = ∅`, then `X ∩ Y = ∅`. So an opaque subterm
contributes `⊤` — every slot — and a pair involving it simply fails to be certified. There is
no third truth value to introduce.

## Both halves of the pair, and two questions for the classifier

`Separates` takes **two** families, one over `Value` and one over `Attr`, and asks each to be
pairwise disjoint. The soundness families stay two: a pair can be
separated on one side and not on the other, and then it is not separated. `held` is the
witness: its write occupancy is its caller-side term's, and its read occupancy is its
stored-side term's. So `union(held(string, number, f, g), string)`, the decimal adapter
against a string, separates on the write side and meets on the read side.

The classifier asks two questions, one for each side. The two coincide below `opaque`: under
`HF`, `occA_le_occV` puts the read occupancy inside the write occupancy under `Member.slot`,
so a held-free pair disjoint on the write side is disjoint on the read side. A `held` has its
two occupancies in two coordinates, and there the read question does work that the write
question cannot.

The specification states the asymmetry for the case that *does* separate — `union(set(string), set(number))`,
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
| slot | the `Value` constructor on the write side, which bounds the `Member` on the read side | `Orth1` |
| names | the presence each body admits at one name, where the two meet at the bottom | `OrthM` |
| literals | one shared required name pinned to disjoint alternatives, at four bases | `OrthS` |
| alternatives | two literals, or two sets over literals, at one base with disjoint `ℓ` | `OrthL` |
| opaque predicate | `refine`'s `q`, `held`'s `f` | undecidable by construction |

The interface the discharger consumes is `Separates`, a `Prop`; `Orth` is the *decidable*
sufficient condition for it, covering the first four phases. Phases *literals* and
*alternatives* are folded in per base, and not uniform in the base. The type is the reason.
`GroundKind.number.Carrier` is the well-formed numerals, a subtype of a `String`, whose
`DecidableEq` is a
field of an axiomatized host. The gate moved into the carrier and the
noncomputability did not move with it, because a `Subtype`'s instance is the base type's. So a
`Bool`-valued test for `ℓ ∩ ℓ' = ∅` uniform in the base is `noncomputable`, and `Orth` stops
reducing in the kernel, which is the whole of its value. `Domain.lean`'s note on
`GroundKind.Carrier` predicts exactly this.

`OrthL` matches the base instead. `string`, `boolean` and `binary` compute, and
`number` answers `false`. The same rows run one spelling further out, at
`refine(set b, each(members k ls))`, which is what `set` taking a base makes of
`set(literal k ls)`. That is the sound direction: `false` means no certificate, and a
caller at the numeric base supplies the premise to `separates_literal_disjoint` by hand. `null` answers `false` too, and there the answer is exact
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

Phase *literals* takes three bases where a tag takes one, and the reason is the difference between
the two questions. A tag rule is about what a key can carry, and a tag is read back as text, so
`string` is the base that can carry one. The meet is about what a value can
satisfy, and a `boolean` or `binary` literal separates two objects as well as any. `number` and
`null` decline here for the reasons `OrthL` gives at the same two bases.
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
    `decide` over these is the whole of what makes `Orth` checkable by `by decide`. -/
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
    * An alternate reader (`Codec.extendRead`) is outside the structural classifier.
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

    An alternate reader is a codec, not a `Term`. The classifier has no alternate-reader
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

/-! ## The classifier -/

/-- **Phase *slot*.** The write occupancies disjoint, and the read occupancies disjoint.

    **Two questions, and they coincide below `opaque`.** A `held` has its two occupancies in
    two coordinates: the write side is the caller-side term's, and the read side is the
    stored-side term's. A held-free term has one coordinate, and there the read occupancy
    lies inside the write occupancy (`occA_le_occV`, under `HF`). The classifier asked the
    write question alone while a held's write occupancy was the top, and that was sound only
    for that reason. -/
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
    ordinary instance applies, while `.number` used to elaborate as a host subtype whose
    instance was a
    field of an axiomatized host. One uniform row would make this `noncomputable`
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
  | .literal .boolean x, .literal .boolean y => decide (x ≠ y)
  | .literal .binary x,  .literal .binary y  => decide (x ≠ y)
  | .literal .null x,    .literal .null y    => decide (x ≠ y)
  -- the numeric carrier's equality used to come from an axiomatised host; see above
  | .literal .number _,   .literal .number _    => false
  -- `set(literal k ls)`, in the spelling `set` taking a base forces on it
  | .refine (.set b) (.each (.members .string ls)),
    .refine (.set b') (.each (.members .string ls'))  => decide (b = b') && disjAlts ls ls'
  | .refine (.set b) (.each (.members .binary ls)),
    .refine (.set b') (.each (.members .binary ls'))  => decide (b = b') && disjAlts ls ls'
  -- `number` declines here for the reason it declines above. `boolean` and `null` have no row
  -- because no set holds them: `liftQ (inL .boolean ls)` is `false` at every wire family, so
  -- such a term admits nothing and there is no pair to certify.
  | _, _ => false

/-- Two literal payloads at one base that are different values. `OrthL` asks this of two terms;
    this asks it of the two payloads a pair of specs pins one name to.

    Three bases and not six, and the rows are the bases for the reason `OrthL` gives: a uniform
    row would be `noncomputable` at `number` and would stop `Orth` reducing at every pair.
    `null` has no row because two null literals carry the one inhabitant of `Unit`. -/
def altsDisj : Option Alts → Option Alts → Bool
  | some ⟨.string, x⟩,  some ⟨.string, y⟩  => decide (x ≠ y)
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
    where a tag takes one. A tag sits at `string` because a tag is read back as
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

theorem specOf_none_admitOptV {t : Term} (v : Value) :
    admitOptV (specOf t, Adm t) v = Adm t v := by simp only [admitOptV]

theorem specOf_none_admitOptA {t : Term} (a : Attr) :
    admitOptA (specOf t, AdmA t) a = AdmA t a := by simp only [admitOptA]

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
  have := List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).1 s (Slot.mem_all s)
  simp_all

theorem occA_disjoint_of_Orth1 {x y : Term} (h : Orth1 x y = true) {m : Member}
    (hx : occA x m = true) (hy : occA y m = true) : False := by
  have := List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2 m (Member.mem_all m)
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
    `Separates`, not a new case in `pairwiseCompat_of_separated`. -/
def Separates (x y : Term) : Prop :=
  (∀ v, OrthSV x v → ¬ OrthSV y v) ∧ (∀ a, OrthSA x a → ¬ OrthSA y a)

/-! ## Phase *alternatives*

Two literals at one base pinned to different values. The `Prop` below is uniform in the base and
`OrthL` decides it at four of the six, for the reason the file header gives. It is the
generalization of the hand instances at one base. -/

/-- Different values make `inL` disjoint, at every base. One base is not the pattern match:

    * `null` — `inL .null _ .null` is `true` unconditionally, so two null literals are never
      disjoint. The premise is what rules it out, *vacuously*: `Unit` has exactly one
      inhabitant, so `x ≠ y` is uninhabited there. The rule needs no `k ≠ .null` side
      condition. -/
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
      -- `number` is ungated again, and this time because the carrier IS the gate
      replace h : decide (d = x) = true := h
      exact decide_eq_false (of_decide_eq_true h ▸ hd)
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

theorem denote_lit (k : GroundKind) (x : k.Carrier) :
    denote (.literal k x) = literalCodec k x := rfl

/-- The literal's read row *is* the codec's read domain — `AdmA_exact` with no hypothesis, so
    this is a rewrite rather than a discharge. It is what makes the read side of the rule
    uniform in the base: `AdmALit` is spelled per base,
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
    rw [specOf_none_admitOptV, Adm_literal] at hx hy
    -- `AdmLit` is `inL`, full stop, since `number`'s `WF` conjunct became its carrier's
    have hix : inL k x v = true := hx
    have hiy : inL k y v = true := hy
    rw [inL_disjoint hd v hix] at hiy
    exact absurd hiy (by simp)
  · rintro a ⟨-, hx⟩ ⟨-, hy⟩
    rw [specOf_none_admitOptA, AdmA_literal] at hx hy
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
    admits `[]`, which passes every element predicate vacuously, so two arrays never separate. -/
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
    rw [specOf_none_admitOptV, Adm_refine_row] at hx hy
    have hlx : liftQ (inLs k ls) v = true := (Bool.and_eq_true_iff.mp hx).2
    have hly : liftQ (inLs k ls') v = true := (Bool.and_eq_true_iff.mp hy).2
    rw [liftQ_inLs_disjoint hd v hlx] at hly
    exact absurd hly (by simp)
  · rintro a ⟨-, hx⟩ ⟨-, hy⟩
    rw [specOf_none_admitOptA, AdmA_refine_row] at hx hy
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

/-- Phase *alternatives*, from its decidable half. One `split` over `OrthL`'s eight rows: four
    hand `separates_literal_disjoint` its premise, two hand `separates_setLiteral_disjoint`
    its premise and the base equality the read side needs, and two answer `false`. -/
theorem separates_of_orthL {x y : Term} (h : OrthL x y = true) : Separates x y := by
  unfold OrthL at h
  split at h
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
    `pairwiseCompat_of_separated` gains no case. -/
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

/-- **Pairwise separation bounds the admitters at one.** Separation says no two options admit
    one input, and admission implies occupancy through `occV_sound`, so the two conjuncts of
    `OrthSV` are both in hand.

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

/-- …and from the decidable classifier. -/
theorem admitsAtMostOne_of_orth {opts : List Term}
    (h : List.Pairwise (fun x y => Orth x y = true) opts) :
    AdmitsAtMostOne (semsOf opts) :=
  admitsAtMostOne_of_separated (separated_of_orth h)

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
  have hsV : admitOptV (specOf s, Adm s) v = true := (Adm_exact s v).mpr ((hlaw s hs).canon hp)
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

/-- …and from the decidable classifier. -/
theorem pairwiseCompat_of_orth {opts : List Term}
    (hlaw : ∀ t ∈ opts, Lawful (denote t))
    (h : List.Pairwise (fun x y => Orth x y = true) opts) : PairwiseCompat opts :=
  pairwiseCompat_of_separated hlaw (separated_of_orth h)

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

Each of these is a pair that `Orth` must not certify. -/

/-- `not_sepJV_array_literals`: `array` admits every length, so
    two arrays both admit `[]` however disjoint their elements. `Orth` answers `false` because
    both occupy `arr` and `L` — and the reason is the same one the hand witness gives, that
    the length set has to come *before* the positions. -/
theorem not_orth_array_literals :
    Orth (.array (.literal .string lsA)) (.array (.literal .string lsB)) = false := by decide

/-- A literal is a refinement of its base, so its slot is its base's. -/
theorem not_orth_literal_string : Orth (.literal .string lsA) .string = false := by decide

/-- `opaque` writes strings — the fact the retired layer's two `opaque`-against-`string`
    refutations carried, kept here where it is decidable. -/
theorem not_orth_opaq_string : Orth .opaq .string = false := by decide

/-- The two options read the member `S`, since the read occupancy
    of a `held` is its stored-side term's. Holds for every caller-side term `P` and every `f`
    and `g`: the read question refuses the pair whatever the write question answers. -/
theorem not_orth_literal_held (P : Term) (f g : Value → Value) :
    Orth (.literal .string lsA) (.held (.literal .string lsB) P f g) = false := by
  simp [Orth, Orth1, OrthM, OrthS, OrthL, occA, occOnly, Member.all, specOf, GroundKind.member]

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

/-- **The numeric base declines, and the pair is still not ambiguous.** The numeric carrier's
    equality came from an axiomatised host, so `OrthL` had no computable row there and answered
    `false`.
    `separates_literal_disjoint` takes the premise by hand instead. -/
theorem not_orth_literal_number (x y : GroundKind.number.Carrier) :
    Orth (.literal .number x) (.literal .number y) = false := by
  simp [Orth, Orth1, OrthM, OrthS, OrthL, occV, occOnly, Slot.all, specOf, GroundKind.slot]

/-- **Two null literals are never disjoint**, and `false` here is exact rather than a
    concession: `NEFinset Unit` has one inhabitant, so both hold `()`. -/
theorem not_orth_literal_null (x y : GroundKind.null.Carrier) :
    Orth (.literal .null x) (.literal .null y) = false := by
  simp [Orth, Orth1, OrthM, OrthS, OrthL, occV, occOnly, Slot.all, specOf, GroundKind.slot]

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
    nothing to compare. ~~The witness was `set(string)` against `set(decimal)`, both writing a
    `strSet`~~; those two part on their slots now, so this pair certifies and the theorem below
    records the separation rather than the gap. A pair that still shows the general point needs
    two bases sharing one slot, and after the numeric carriers merged there is no such pair. -/
theorem orth_set_literals_two_bases :
    Orth (.refine (.set .string) (.each (.members .string setA)))
         (.refine (.set .number) (.each (.members .string setB))) = true := by decide

/-- **A `closure` beside a `members` is not certified**, which is the case `Pred` keeps rather
    than removes. Holds for every `q`, so this is phase *opaque predicate* and not a gap. -/
theorem not_orth_set_literal_closure (q : Value → Bool) :
    Orth (.refine (.set .string) (.each (.members .string setA)))
         (.refine (.set .string) (.each (.closure q))) = false := by
  simp [Orth, Orth1, OrthM, OrthS, OrthL, occV, occOnly, Slot.all, specOf, SetBase.slot]

end Calculus
