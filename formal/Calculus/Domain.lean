import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
/-!
# §1 — The attribute domain

Mechanization of `docs/codec-calculus.md`. Modelling choices, each recorded where it bites:

* `Numeral` is `String`, with §1's grammar/bounds as the decidable predicate `Numeral.WF`
  below. The carrier stays unrestricted on purpose — `decimal` is what checks.
* Wire sets (`SS`/`NS`/`BS`) and maps (`M`) are lists: a quotient type cannot occur
  recursively inside an inductive, and the laws never inspect order — the quotient of §2
  (`ker p`) is where set-ness lives, not in the carrier.
* `Double` is axiomatized with exactly the shortest-text round trip the doc's `(number)`
  case consumes. That is an IEEE-754 fact, not a theorem of this calculus.
-/

namespace Calculus

/-- Attribute names. -/
abbrev Name := String

/-- Numeral *text*. Every string is one; §1's `Numerals` is the subset `Numeral.WF` picks
    out, and `WFNumeral` below is that subset as a type. `Attr.n` carries the subtype, so
    the attribute domain is exactly §1's — this abbreviation is the raw text a parser sees,
    not the carrier of an `N`. -/
abbrev Numeral := String

/-- Byte strings. -/
abbrev Bytes := List UInt8

/-! ## §1's `Numerals`

The table in §1 states three clauses: "optional sign, digits, optional point, optional
exponent; ≤ 38 significant digits; magnitude 0 or `1e-130 … 9.9…e125`". All three are
modelled here, as a decidable predicate on the carrier.

`Numeral` stays `String` as the *text* type, and `WFNumeral` — the subtype `WF` cuts out —
is what `Attr.n` carries. So `⟨N, "abc"⟩` is not an attribute at all, and `Carries(N)` in
§1's coproduct is exact rather than approximated. This document argued for a while that the
carrier should stay unrestricted so that a port would see the embedding `⌈·⌉` is partial;
that partiality is a fact about the **port's** types, not the model's, and nothing in the
development ever used an ill-formed `N`. See `codec-formalization.md` §4.

Note the read side has to check too, not merely the write side. If `p` accepted an
ill-formed numeral it would return a value `e` then refuses, breaking **(C)** — so the
grammar is forced onto both halves by the laws, not by taste.

One simplification, narrowing rather than widening: a bare integer part is required, so
`".5"` and `"1."` are rejected. The reason first given for that was wrong — DynamoDB
*accepts* both and normalises them to `"0.5"` and `"1"` (`src/codec.dynamodb.spec.ts`). The
narrowing stands, because `Stored` below rejects them anyway, but it is a narrowing of §1
rather than a transcription of it. Significance is counted between the first and last
nonzero digit, which is the trimming DynamoDB documents.

**`WF` is what DynamoDB accepts; `Stored` is what it hands back.** They are different
sets, and the difference is not cosmetic — see below. -/

namespace Numeral

/-- The longest digit prefix, paired with the rest. -/
def spanDigits : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
    if c.isDigit then
      let (ds, rest) := spanDigits cs
      (c :: ds, rest)
    else ([], c :: cs)

def digitsToNat (ds : List Char) : Nat :=
  ds.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

/-- An optional leading sign. -/
def stripSign : List Char → List Char
  | '+' :: cs => cs
  | '-' :: cs => cs
  | cs => cs

/-- The optional exponent, which must be the whole of the remaining text. -/
def parseExp : List Char → Option Int
  | [] => some 0
  | c :: cs =>
    if c == 'e' || c == 'E' then
      let (neg, ds0) :=
        match cs with
        | '+' :: r => (false, r)
        | '-' :: r => (true, r)
        | r => (false, r)
      let (ds, rest) := spanDigits ds0
      if ds.isEmpty || !rest.isEmpty then none
      else some (if neg then -(digitsToNat ds : Int) else (digitsToNat ds : Int))
    else none

/-- A numeral, taken apart: the digits either side of the point, and the exponent. -/
structure Parsed where
  intDigits : List Char
  fracDigits : List Char
  exp : Int

def parse (s : Numeral) : Option Parsed :=
  let cs := stripSign s.data
  let (ip, r1) := spanDigits cs
  if ip.isEmpty then none
  else
    match r1 with
    | '.' :: r2 =>
      let (fp, r3) := spanDigits r2
      if fp.isEmpty then none else (parseExp r3).map (fun e => ⟨ip, fp, e⟩)
    | _ => (parseExp r1).map (fun e => ⟨ip, [], e⟩)

def mantissa (p : Parsed) : List Char := p.intDigits ++ p.fracDigits

def dropLeadingZeros : List Char → List Char
  | '0' :: cs => dropLeadingZeros cs
  | cs => cs

def dropTrailingZeros (ds : List Char) : List Char :=
  (dropLeadingZeros ds.reverse).reverse

/-- The digits that count: from the first nonzero to the last. -/
def significand (p : Parsed) : List Char :=
  dropTrailingZeros (dropLeadingZeros (mantissa p))

def isZero (p : Parsed) : Bool := (significand p).isEmpty

/-- The power of ten of the leading significant digit — the quantity §1's magnitude
    bound is stated on. -/
def decExp (p : Parsed) : Int :=
  let m := mantissa p
  let leading := m.length - (dropLeadingZeros m).length
  (p.intDigits.length : Int) - 1 - (leading : Int) + p.exp

/-- §1's `Numerals`: the grammar, 38 significant digits, and DynamoDB's magnitude range —
    what the service **accepts** in an `N`. -/
def WF (s : Numeral) : Bool :=
  match parse s with
  | none => false
  | some p =>
    decide ((significand p).length ≤ 38) &&
      (isZero p || (decide (-130 ≤ decExp p) && decide (decExp p ≤ 125)))

/-! ### What the store hands back

§2 composes a codec's `e` and `p` directly. In use there is a **store** between them, and
it is not the identity on attributes: DynamoDB normalises every `N` it accepts — trimming
leading and trailing zeros, dropping `+`, expanding exponents, and keeping one spelling of
zero. Measured rather than assumed: `src/codec.dynamodb.spec.ts` puts each of these forms into a
real table and reads it back, and the two theorems below are that measurement.

Write `η` for the store's normalisation. A codec survives the round trip through the store
exactly when **`η` lies inside `ker p`** — §2's `≈c`, the relation that already exists for
"a different attribute that reads to the same value". `number` satisfies it for free:
`p "1.500"` and `p "1.5"` are the same double. `decimal` cannot, because its `p` is the
identity on the digits, so `ker p` is equality and `η` would have to be too.

So `decimal`'s held set is not `Numerals`. It is the numerals the store returns unchanged,
and that is what this predicate is.

`η ⊆ ker p` is no longer only prose. `Codec.Ker` names §2's `≈c` and `SurvivesStore` names
the inclusion, both in `Codec.lean`; `Lawful.retract_through_store` is what they buy, which
is **(R)** with the store in the middle. The two halves for `decimal` are
`survivesStore_decimalCodec` — the narrowing discharges the premise, because a normalisation
fixes its own normal forms — and `not_survivesStore_decimalWF` in `Refutations.lean`, which
is the codec that gated on `WF` instead, failing on `"1.500"`. `ker_decimalCodec` is the fact
both turn on: `decimal`'s kernel is equality, so nothing weaker than "η fixes it" would
serve. -/

/-- Digits with no leading zero — or exactly `"0"`. -/
def normalInt : List Char → Bool
  | [] => false
  | ['0'] => true
  | '0' :: _ :: _ => false
  | ds => ds.all Char.isDigit

/-- Fraction digits: at least one, all digits, and the last one not a zero. -/
def normalFrac (ds : List Char) : Bool :=
  match ds.getLast? with
  | none => false
  | some d => ds.all Char.isDigit && d != '0'

/-- A magnitude in the form the store returns: no exponent, no leading zeros, no trailing
    fractional zeros. -/
def normalMag (cs : List Char) : Bool :=
  let (ip, r) := spanDigits cs
  normalInt ip &&
    match r with
    | [] => true
    | '.' :: fp => normalFrac fp
    | _ => false

/-- **What DynamoDB stores.** `WF` says the service accepts the string; this says it hands
    the same string back. The sign is refused on zero, because `"-0"` comes back `"0"`. -/
def Normal (s : Numeral) : Bool :=
  match s.data with
  | '-' :: cs => normalMag cs && !(cs == ['0'])
  | cs => normalMag cs

/-- `decimal`'s held set: accepted *and* returned unchanged. -/
def Stored (s : Numeral) : Bool := WF s && Normal s

/-- What the store hands back, it also accepts — so a `Stored` numeral is a `WFNumeral`
    without further checking. `decimal` needs this now that `Attr.n` carries the proof. -/
theorem stored_wf {s : Numeral} (h : Stored s = true) : WF s = true := by
  simp only [Stored, Bool.and_eq_true] at h; exact h.1

/-- The measured table's left column — written, and returned as something else. Every row
    that changed is a row `Stored` must reject. -/
theorem stored_rejects_denormal :
    (Stored "1.500" = false) ∧ (Stored "007" = false) ∧ (Stored "+1" = false) ∧
      (Stored "1e5" = false) ∧ (Stored "-0" = false) ∧ (Stored "0.0" = false) ∧
      (Stored "1.0" = false) ∧ (Stored ".5" = false) ∧ (Stored "1." = false) ∧
      (Stored "01" = false) := by decide

/-- And the rows that came back as written. -/
theorem stored_accepts_normal :
    (Stored "0" = true) ∧ (Stored "1.5" = true) ∧ (Stored "0.5" = true) ∧
      (Stored "10" = true) ∧ (Stored "100" = true) ∧ (Stored "-1.5" = true) ∧
      (Stored "0.0000001" = true) ∧ (Stored "1000000000000000000000" = true) := by decide

/-- The two sets really do differ: the service accepts strings it will not hand back. -/
theorem stored_lt_wf : ∃ s, WF s = true ∧ Stored s = false := ⟨"1.500", by decide⟩

end Numeral

/-- IEEE-754 binary64, opaque. -/
axiom Double : Type

/-- Shortest decimal text reading back as the same double. -/
axiom Double.toDec : Double → Numeral

/-- Read a numeral as a double (rounding), where the magnitude admits one. -/
axiom Double.ofDec : Numeral → Option Double

/-- The §3 `(number)` round trip: shortest text re-reads exactly. -/
axiom Double.roundtrip : ∀ d : Double, Double.ofDec (Double.toDec d) = some d

/-- Equality of doubles is decidable (bit patterns; NaN excluded from the model). -/
axiom Double.decEq : DecidableEq Double

attribute [instance] Double.decEq

/-- **Kinds.** The eight shapes the value language is partitioned into — and the eight
    the attribute domain collapses onto, since the three wire sets are one kind and the
    ten members are eight. A value and the attribute it is written to have the same
    kind: that is what "self-identifying" means in §3's `(opaque)`, and it is the
    disjointness §5's `κ` table is stated in. -/
inductive Kind where
  | string | number | boolean | binary | set | array | map | null
deriving DecidableEq, Repr

/-- The ten members of the coproduct (§1). -/
inductive Member where
  | S | N | B | BOOL | NULL | SS | NS | BS | L | M
deriving DecidableEq, Repr

/-- §1's `℘⁺fin(α)` — the **nonempty** finite subsets. The reference: *"DynamoDB does not
    support empty sets"*, and §1 types all three wire sets as `℘⁺fin`. Carried by the type
    rather than gated by a codec, for the same reason unorderedness and uniqueness are:
    `{S : Finset α // S.Nonempty}` is admissible in a constructor, so the claim that only
    a gate could enforce this was a claim worth testing. -/
abbrev NEFinset (α : Type) := {S : Finset α // S.Nonempty}

/-- §1's `Numerals` — the strings DynamoDB accepts in an `N`, carried by the type. So
    `Carries(N)` is exact and `⟨N, "abc"⟩` is not an attribute at all.

    This was the last of §5's four refined members to be typed, and the argument against
    typing it — that the *carrier* should stay unrestricted so that a port sees the
    embedding `⌈·⌉` is partial — turned out to be load-bearing on nothing: an ill-formed
    numeral appeared in four comments of this development and in no theorem of it. C1's
    insight survives intact, and is sharper for the change: it is the **port's** attribute
    type that is unrefined, not the model's. -/
abbrev WFNumeral := {x : Numeral // Numeral.WF x = true}

/-- A literal numeral, with §1's check discharged where it is written. `WF` is decidable
    by construction, so a concrete numeral carries its own proof and no witness in this
    development had to change shape. -/
def WFNumeral.of (x : Numeral) (h : Numeral.WF x = true := by decide) : WFNumeral := ⟨x, h⟩

@[simp] theorem WFNumeral.of_val (x : Numeral) (h : Numeral.WF x = true) :
    (WFNumeral.of x h).1 = x := rfl

/-- A literal `℘⁺fin`, written as one element and the rest: `insert` is never empty, so
    the proof is discharged by construction rather than at each use site. -/
def NEFinset.of {α : Type} [DecidableEq α] (x : α) (S : Finset α) : NEFinset α :=
  ⟨insert x S, Finset.insert_nonempty x S⟩

theorem NEFinset.mem_of {α : Type} [DecidableEq α] (x : α) (S : Finset α) :
    x ∈ (NEFinset.of x S).1 := Finset.mem_insert_self x S

/-- …and its carrier is the `insert`, so `simp` sees through a literal without every
    call site naming `NEFinset.of` in its own simp set. -/
@[simp] theorem NEFinset.of_val {α : Type} [DecidableEq α] (x : α) (S : Finset α) :
    (NEFinset.of x S).1 = insert x S := rfl

/-- The attribute domain `𝔸` (§1). The coproduct is exact: one member per attribute. -/
inductive Attr where
  | s    (v : String)
  | n    (v : WFNumeral)
  | b    (v : Bytes)
  | bool (v : Bool)
  | null
  /-- §1's `℘⁺fin(String)`. A `Finset` and not a list: the reference says the order of a
      set's values is not preserved and each value is unique, and the store dedups on
      insert. Both facts are properties of the *type*, not obligations on a codec. -/
  | ss   (v : NEFinset String)
  | ns   (v : NEFinset WFNumeral)
  | bs   (v : NEFinset Bytes)
  | l    (v : List Attr)
  /-- §1's `M`. The reference calls it an *unordered* collection of name-value pairs, and
      an update at an existing name replaces it — so the names form a **set** and the
      values are a function on it. A list would admit two orderings of one map and a
      repeated name, neither of which `M` has.

      `Finset Name` is admissible because `Name` is concrete; the values sit in the
      function's codomain, which is a strictly positive position. What is *not* admissible
      is `Finset (Name × Attr)` — that nests the type under declaration. -/
  | m    (keys : Finset Name) (f : {k // k ∈ keys} → Attr)

/-- The member an attribute carries. -/
def Attr.member : Attr → Member
  | .s _    => .S
  | .n _    => .N
  | .b _    => .B
  | .bool _ => .BOOL
  | .null   => .NULL
  | .ss _   => .SS
  | .ns _   => .NS
  | .bs _   => .BS
  | .l _    => .L
  | .m _ _  => .M

/-- The kind an attribute is of: its member, with `SS`/`NS`/`BS` identified. -/
def Attr.kind : Attr → Kind
  | .s _    => .string
  | .n _    => .number
  | .b _    => .binary
  | .bool _ => .boolean
  | .null   => .null
  | .ss _ | .ns _ | .bs _ => .set
  | .l _    => .array
  | .m _ _  => .map

/-- An item: an `M` without its wrapper (§1). -/
abbrev Item := List (Name × Attr)

/-- The value language, partitioned exactly as §5's `Kind`. `decimal` holds numerals as
    `str` values — one string kind, as in the doc's κ table. -/
inductive Value where
  | str  (v : String)
  | num  (v : Double)
  | bool (v : Bool)
  | bin  (v : Bytes)
  | null
  /-- The reference: "The set types are string set, number set, and binary set." Three
      concrete element types, so each is a genuine `Finset`. -/
  | strSet (v : NEFinset String)
  | numSet (v : NEFinset Double)
  | binSet (v : NEFinset Bytes)
  | arr  (v : List Value)
  /-- …and the value side of the same, for the same reason. -/
  | map  (keys : Finset Name) (f : {k // k ∈ keys} → Value)

/-- The kind a value is of — §5's `κ` reads this. -/
def Value.kind : Value → Kind
  | .str _  => .string
  | .num _  => .number
  | .bool _ => .boolean
  | .bin _  => .binary
  | .null   => .null
  | .strSet _ => .set
  | .numSet _ => .set
  | .binSet _ => .set
  | .arr _  => .array
  | .map _ _ => .map

/-! ## A value with a ground base (§3 `(literal)`'s payload)

`(literal)` has always had a `g ground` premise, and the model carried it *twice*: as
`literalOK`'s `| _ => false` and as `literalMember`'s `none`. Neither is content. Both say
only *"this value has a ground base"* — a claim about the payload's carrier, which is what a
payload's **type** is for.

So the payload has one. `GroundValue.member` is total where `literalMember` was partial,
`literalCodec` has no `Codec.empty` case to fall into, and the rule's `hμ` premise does not
exist to be discharged. What is left of `literalOK` is `Numeral.WF` at `.num`, which is
§3's `ℓ ⊆ D` and is content — the same premise `(literal-N)` carries as `hD`, at arity one. -/

/-- The five ground kinds, as a carrier. `Value`'s scalar constructors and no others: a set,
    an array and a map are exactly what `(literal)` cannot hold, and now cannot be handed. -/
inductive GroundValue where
  | str  (v : String)
  | num  (v : Double)
  | bool (v : Bool)
  | bin  (v : Bytes)
  | null

/-- The value it is. Injective by construction — five constructors onto `Value`'s five
    scalars — so nothing about `(literal)`'s held set changes except that it is now written
    through an embedding. -/
@[simp] def GroundValue.toValue : GroundValue → Value
  | .str s  => .str s
  | .num d  => .num d
  | .bool b => .bool b
  | .bin b  => .bin b
  | .null   => .null

/-- §5's `κ` on the payload. Agrees with `Value.kind` through the embedding, by `rfl`. -/
@[simp] def GroundValue.kind : GroundValue → Kind
  | .str _  => .string
  | .num _  => .number
  | .bool _ => .boolean
  | .bin _  => .binary
  | .null   => .null

/-- §3 `(literal)`'s member: the one its base stores as. **Total**, which is the point —
    `literalMember : Value → Option Member` was this function plus a `none` meaning "this
    payload has no ground base", and that sentence is now unsayable. -/
@[simp] def GroundValue.member : GroundValue → Member
  | .str _  => .S
  | .num _  => .N
  | .bool _ => .BOOL
  | .bin _  => .B
  | .null   => .NULL

end Calculus
