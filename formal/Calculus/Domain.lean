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

/-- Wire numerals (§1 `Numerals`). The *carrier* is every string — `Attr.n "abc"` stays
    representable, because §1 describes what DynamoDB accepts, not what Lean can build.
    Well-formedness (grammar, 38 digits, magnitude) is `Numeral.WF` below, and
    `decimalCodec` gates on it. -/
abbrev Numeral := String

/-- Byte strings. -/
abbrev Bytes := List UInt8

/-! ## §1's `Numerals`

The table in §1 states three clauses: "optional sign, digits, optional point, optional
exponent; ≤ 38 significant digits; magnitude 0 or `1e-130 … 9.9…e125`". All three are
modelled here, as a decidable predicate on the carrier.

`Numeral` stays `String` — the *carrier* is unrestricted, so `Attr.n "abc"` remains
representable — and well-formedness is what `decimal` checks. That is the honest split:
§1 describes which strings DynamoDB will accept in an `N`, and the calculus's job is that
its codecs write only those. `typed_e_mem` is what reports it.

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

/-- The attribute domain `𝔸` (§1). The coproduct is exact: one member per attribute. -/
inductive Attr where
  | s    (v : String)
  | n    (v : Numeral)
  | b    (v : Bytes)
  | bool (v : Bool)
  | null
  /-- §1's `℘⁺fin(String)`. A `Finset` and not a list: the reference says the order of a
      set's values is not preserved and each value is unique, and the store dedups on
      insert. Both facts are properties of the *type*, not obligations on a codec. -/
  | ss   (v : Finset String)
  | ns   (v : Finset Numeral)
  | bs   (v : Finset Bytes)
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
  | strSet (v : Finset String)
  | numSet (v : Finset Double)
  | binSet (v : Finset Bytes)
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

end Calculus
