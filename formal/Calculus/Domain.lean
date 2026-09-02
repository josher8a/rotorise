import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
-- `Finset.sup`, for `Attr.nesting` at `M`: the names are a set, so the layer below is a
-- supremum over the key set and not a fold down a list. `Opaque.lean` imports it for the
-- same reason at `Attr.depth`.
import Mathlib.Data.Finset.Lattice.Fold
/-!
# §1 — The attribute domain

Mechanization of `docs/codec-calculus.md`. Modelling choices, each recorded where it bites:

* `Numeral` is `String` — the *raw text a parser sees*. The carrier is not: `Attr.n`
  carries `WFNumeral`, the subtype `Numeral.WF` picks out, so `⟨N, "abc"⟩` is
  unrepresentable rather than merely unwritten. `decimal` still gates, at `Stored`, which
  is a narrower question than well-formedness.
* Wire sets (`SS`/`NS`/`BS`) are `NEFinset` of a *concrete element type* — `NEFinset
  String`, `NEFinset WFNumeral`, `NEFinset Bytes`, and the same three on `Value`. Maps
  (`M`) are a `Finset Name` with a function on it. Unordered, unique and non-empty are
  properties of the type, so set-ness lives in the carrier and not in §2's `ker p`. The
  kernel's restriction is narrower than it looks: it rejects a `Finset` whose element type
  is the datatype being declared, which is why `union`'s payload is still a list (§11.5 of
  `codec-audit.md`), and accepts one over a concrete type in the same constructor.
* `Double` is axiomatized with exactly the shortest-text round trip the doc's `(number)`
  case consumes. That is an IEEE-754 fact, not a theorem of this calculus. It is asserted as
  *one* thing — `numericHost : NumericHost Double` — so what the calculus assumes about
  numbers is an interface a reader can inspect and inhabit, rather than five axioms that
  must be collected before the question can even be asked.
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
fixes its own normal forms — and `not_survivesStore_wfDecimalCodec` in `Refutations.lean`, which
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

/-! ### The numeric host, as an interface rather than five assumptions

This block used to be five axioms — a type, two functions, a round trip and a
`DecidableEq` — and every one of them said "binary64" in its docstring while asserting
nothing of the sort. Five separate assertions cannot be *inspected*: a reader asking "what
exactly is assumed about the host?" had to collect them, and nothing in the development
could quantify over the answer.

`NumericHost` is that answer, as one structure. The axiom block below is then two lines —
a type, and the claim that it carries the interface — and the `Double.*` names are
`def`s projecting out of it, so every call site is unchanged. What this buys is not the
count. It is that the assumption is now a **first-class object**, so the claim the block
was always making — *the calculus does not depend on binary64, only on a host with a
decimal spelling that re-reads* — becomes checkable. `numericHost_wfNumeral` and
`numericHost_unit` below are two inhabitants with provably different decimal images, and
the first needs no `Double` axiom at all. -/

/-- **What §1 assumes of the numeric host, and all it assumes.** A decimal spelling, a
    partial reader, the round trip §3's `(number)` needs, and decidable equality. -/
structure NumericHost (D : Type) where
  /-- Shortest decimal text reading back as the same element. -/
  toDec : D → Numeral
  /-- Read a numeral (rounding), where the magnitude admits one. -/
  ofDec : Numeral → Option D
  /-- The §3 `(number)` round trip: shortest text re-reads exactly. -/
  roundtrip : ∀ d, ofDec (toDec d) = some d
  /-- Equality is decidable (bit patterns, for binary64; NaN excluded from the model). -/
  decEq : DecidableEq D

/-- IEEE-754 binary64, opaque. -/
axiom Double : Type

/-- …and the whole of what is assumed about it: that it is a `NumericHost`. -/
axiom numericHost : NumericHost Double

/-- Shortest decimal text reading back as the same double. -/
noncomputable def Double.toDec : Double → Numeral := numericHost.toDec

/-- Read a numeral as a double (rounding), where the magnitude admits one. -/
noncomputable def Double.ofDec : Numeral → Option Double := numericHost.ofDec

/-- The §3 `(number)` round trip: shortest text re-reads exactly. -/
theorem Double.roundtrip : ∀ d : Double, Double.ofDec (Double.toDec d) = some d :=
  numericHost.roundtrip

/-- Equality of doubles is decidable (bit patterns; NaN excluded from the model). -/
noncomputable def Double.decEq : DecidableEq Double := numericHost.decEq

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

/-! **Do not reach for an order on these.** A wire set read back as a *list* would need a
canonical representative, hence a sort, hence an order — and `LinearOrder String` and
`List.sorted_insertionSort` both depend on `Classical.choice`, which the axiom base
`docs/codec-formalization.md` §3 advertises does not include. `#assert_axioms_all` is what
caught it, and `Calculus/WireOrder.lean` was 247 lines of axiom-free order built to get around
it.

None of that is needed any more, and the reason is this abbreviation: both sides of every wire
set are now a `Finset` of a *concrete element type* — `NEFinset String`, `NEFinset Double`,
`NEFinset Bytes` on `Value`, the same on `Attr` — so there is no list to sort and no
representative to choose. The file is deleted; this note is the part of it that was load-bearing.
-/

/-- §1's `Numerals` — the strings DynamoDB accepts in an `N`, carried by the type. So
    `Carries(N)` is exact and `⟨N, "abc"⟩` is not an attribute at all.

    This was the last of §5's four refined members to be typed, and the argument against
    typing it — that the *carrier* should stay unrestricted so that a port sees the
    embedding `⌈·⌉` is partial — turned out to be load-bearing on nothing: an ill-formed
    numeral appeared in four comments of this development and in no theorem of it. C1's
    insight survives intact, and is sharper for the change: it is the **port's** attribute
    type that is unrefined, not the model's. -/
abbrev WFNumeral := {x : Numeral // Numeral.WF x = true}

/-- A numeral in the form the store hands back — §1's `Stored`, carried rather than gated.

    This is `decimal`'s literal carrier, and the reason `decimal` is worth a ground base of its
    own. At `number` the alternatives are `Double`s and `(literal)`'s premise `ℓ ⊆ D` is a *gate*
    outside the carrier, which is why `adm (.literal .number ls)` over-approximates by exactly
    that conjunct. Here the gate is the subtype, so `inL` is the whole of admission and the row
    is exact by construction. -/
abbrev StoredNumeral := {s : Numeral // Numeral.Stored s = true}

/-- A literal numeral, with §1's check discharged where it is written. `WF` is decidable
    by construction, so a concrete numeral carries its own proof and no witness in this
    development had to change shape. -/
def WFNumeral.of (x : Numeral) (h : Numeral.WF x = true := by decide) : WFNumeral := ⟨x, h⟩

@[simp] theorem WFNumeral.of_val (x : Numeral) (h : Numeral.WF x = true) :
    (WFNumeral.of x h).1 = x := rfl

/-! ### Two inhabitants, so the interface is checkably an interface

An axiom block with no models is indistinguishable from an assumption. These two are the
evidence that `NumericHost` is the weaker thing it claims to be — a *signature the calculus
programs against* — rather than binary64 under another name. -/

/-- **The arbitrary-precision host.** `WFNumeral` is its own decimal spelling, so the
    adapter is the identity and the round trip is `dif_pos` on the subtype's own proof.
    Note what is *not* imported here: this model needs no `Double` axiom, so every theorem
    of §1 that is really about the interface holds of a host with no rounding at all. -/
def numericHost_wfNumeral : NumericHost WFNumeral where
  toDec := Subtype.val
  ofDec := fun x => if h : Numeral.WF x = true then some ⟨x, h⟩ else none
  roundtrip := fun d => by simp [d.2]
  decEq := inferInstance

/-- **The one-number host**, at the other extreme: a single element, spelled `"0"`. Total
    on nothing but its own spelling, and still a lawful `NumericHost`. -/
def numericHost_unit : NumericHost Unit where
  toDec := fun _ => "0"
  ofDec := fun x => if x = "0" then some () else none
  roundtrip := fun _ => rfl
  decEq := inferInstance

/-- **And their decimal images differ**, which is what makes the pair evidence rather than
    decoration: `"1.5"` is the spelling of an element of the first host and of no element of
    the second. A property provable from `NumericHost` alone therefore cannot decide how
    many numbers the host has, nor which decimals it spells — which is exactly the
    independence the axiom block asserts and could not previously exhibit. -/
theorem numericHost_images_differ :
    (∃ d, numericHost_wfNumeral.toDec d = "1.5") ∧
      (∀ u, numericHost_unit.toDec u ≠ "1.5") :=
  ⟨⟨WFNumeral.of "1.5", rfl⟩, fun _ => by simp [numericHost_unit]⟩

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

/-! ## §1's nesting bound — the one constraint on `𝔸` the carrier cannot carry

`docs/dynamo-datatypes.md:130`: *"The document types are list and map. These data types can
be nested within each other, to represent complex data structures up to 32 levels deep."*

A subtype `{as : List Attr // Attr.nestingL as ≤ 31}` puts `Attr` under its own declaration
and the kernel refuses it, exactly as it refuses `Finset Attr`. So `Attr` above is the
*unbounded* closure and the bound is stated about it rather than inside it. §6 of
`codec-audit.md` recorded that as "not typeable" and stopped there; being un-typeable never
made it un-checkable, and `src/` had to gate on it in the end (§12.6).

**It counts `L` and `M` and nothing else.** A scalar is not a document type. Neither is a
wire set: `SS`/`NS`/`BS` carry payloads rather than attributes, so a set can neither nest
nor be nested in, and one sitting at the deepest legal level is legal. That is what makes
this a **different function from `Attr.depth`** (`Opaque.lean`), which is a termination
measure and charges a wire set a layer for the payloads it recurses past. The measure is
the wrong thing to bound: it would refuse a legal set. The two must not be conflated, and
this docstring is where that is written down. -/

mutual

/-- How many document types an attribute nests. -/
def Attr.nesting : Attr → Nat
  | .s _ | .n _ | .b _ | .bool _ | .null => 0
  | .ss _ | .ns _ | .bs _ => 0
  | .l as => Attr.nestingL as + 1
  -- as at `Attr.depth`: `M` is a key set with a function on it, so the layer below is a
  -- `Finset.sup` over the keys rather than a fold down a list.
  | .m keys f => (keys.attach.sup fun k => Attr.nesting (f k)) + 1

/-- The elements' nesting — the list mirror `Attr.nesting` needs at `L`. Empty is `0`, so
    `Attr.nesting (.l []) = 1`: an empty list is still one document. -/
def Attr.nestingL : List Attr → Nat
  | [] => 0
  | a :: as => max (Attr.nesting a) (Attr.nestingL as)

end

/-- The reference's number, named once. -/
def maxNesting : Nat := 32

/-- **§1's `𝔸` as the store actually has it.** The `Attr` above is what the calculus writes
    into; this is the subset DynamoDB accepts. Everything else in §1 is exact, so this
    predicate is the whole of the difference — and `ran(e) ⊆ 𝔸` is only the guarantee it
    reads as when the two agree. -/
def Attr.Storable (a : Attr) : Prop := Attr.nesting a ≤ maxNesting

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

/-! ## The ground bases, and what each one carries (§3 `(literal)`'s payload)

§3 has **one** `(literal)` rule:

```
⊢ g : T ⇝ μ,  g ground    ℓ₁ … ℓₙ ∈ T,  n ≥ 1,  pairwise distinct
───────────────────────────────────────────────────────────────── (literal)
⊢ literal(ℓ₁ … ℓₙ) : {ℓ₁ … ℓₙ} ⇝ μ
```

The model had three constructors for it — arity-one over a `Value`, and two n-ary ones at the
two commonest bases — and every part of that premise line was a gate. `g ground` was carried
three times over (`literalOK`'s `| _ => false`, `literalMember`'s `none`, `literalCodec`'s
`Codec.empty`); `n ≥ 1` and pairwise distinctness were `hne`/`hnd` until `℘⁺fin` typed them;
`ℓᵢ ∈ T` at a base the other constructors could not name was why there were two of them.

`GroundKind` is the premise line as a type. The base is an index, so `member` is a function of
it and `g ground` is unsayable-otherwise; the alternatives are a `NEFinset` of *that base's*
carrier, so non-emptiness, distinctness and homogeneity are all the type's. One constructor, and
arity one is the singleton case.

`Calculus/LiteralArity1.lean` is why it is this shape rather than a union of arity-one literals:
the union is derivable, but `Term.union` is list-shaped and the bridge from a `Finset` is
`Classical.choice`. See `docs/codec-audit.md` §11. -/

/-- The five bases a literal can sit at — `Kind` minus the three container kinds. -/
inductive GroundKind where
  | string | number | decimal | boolean | binary | null
deriving DecidableEq, Repr

/-- What each base's held set is drawn from. `Unit` at `.null` is not a degenerate case: the
    only nonempty subset of `Unit` is `{()}`, so `NEFinset .null.Carrier` says "exactly null"
    and cannot say anything else.

    **Reducible**, and that is load-bearing: it lets `Carrier .string` elaborate as `String`, so
    membership in `ℓ` resolves through `String.decEq` and the ordinary instances. An indexed
    `DecidableEq k.Carrier` instance would work too, and would be *noncomputable* — `Double`'s
    equality is a field of §1's axiomatized `NumericHost` — which then spreads to every `def`
    that names a literal. -/
@[reducible] def GroundKind.Carrier : GroundKind → Type
  | .string  => String
  | .number  => Double
  -- §1's stored numerals, as a subtype. See `StoredNumeral`: the gate `number` carries as a
  -- premise is this base's carrier, which is the whole point of having the base.
  | .decimal => StoredNumeral
  | .boolean => Bool
  | .binary  => Bytes
  | .null    => Unit

/-- An alternative, as the value it is. Injective at every base. -/
@[simp] def GroundKind.toValue : (k : GroundKind) → k.Carrier → Value
  | .string,  s => .str s
  | .number,  d => .num d
  -- `decimal` holds its numeral as *text* and stores it as `N`; the value side is a `.str`,
  -- which is exactly why `GroundKind` indexes value carriers and `SetBase` could not reuse it.
  | .decimal, x => .str x.1
  | .boolean, b => .bool b
  | .binary,  b => .bin b
  | .null,    _ => .null

/-- §3 `(literal)`'s member: the one the base stores as. **Total**, and a function of the index
    rather than an index with a premise pinning it — which is the `hμ` the three constructors
    between them carried. -/
@[simp] def GroundKind.member : GroundKind → Member
  | .string  => .S
  | .number  => .N
  | .decimal => .N
  | .boolean => .BOOL
  | .binary  => .B
  | .null    => .NULL

/-- §5's `κ` on a literal: the base's kind. -/
@[simp] def GroundKind.kind : GroundKind → Kind
  | .string  => .string
  | .number  => .number
  -- the *value*'s kind, and a decimal literal's values are strings — so it shares `κ` with
  -- `string` and is told apart from it by the member, not the kind.
  | .decimal => .string
  | .boolean => .boolean
  | .binary  => .binary
  | .null    => .null

/-! ## The set bases (§3 `(set)`'s payload)

§3's `(set)` rule reads a member off its element term and refuses when there is none. Four
element terms have one — `string`, `number`, `decimal`, `binary` — and every other element
term the constructor accepted was either underivable (`setMember` is partial) or unreachable
in `src/`. `SetBase` is those four as an index, so the rule's member premise becomes a
function of the index and `set(union(…))` is unstatable rather than merely underivable.

**Four bases onto three wire members.** `number` and `decimal` both store `NS`; they are not
the same base and neither is redundant. `number` is a caller's platform number — §1's `D`
reached through `Double.toDec` — and `decimal` is the host-independent spelling, carried as a
`Numerals` string on the value side. Collapsing them would delete the only base whose value
side is exact, and `Member` cannot tell them apart (both `NS`), which is why the index is
neither `Member` nor `GroundKind`: `GroundKind` **indexes value carriers**, and `set(decimal)`
is a `strSet` there while it is an `NS` on the wire.

    This used to give a second reason — *"`GroundKind` has no `decimal`"* — and it was true when
    written and false seventy lines above, from the commit that added `.decimal` to the inductive.
    Only the carrier half was ever load-bearing, so the conclusion is untouched; the dead reason
    is what a description costs when nothing keeps it honest. -/

/-- The four bases a set's elements may sit at. -/
inductive SetBase where
  | string | number | decimal | binary
deriving DecidableEq, Repr

/-- The wire member a set at this base stores as — §3 `(set)`'s `μS`, now a total function
    of the index where it was a premise (`setMember μ = some μS`). Not injective: `number`
    and `decimal` share `NS`. -/
@[simp] def SetBase.member : SetBase → Member
  | .string  => .SS
  | .number  => .NS
  | .decimal => .NS
  | .binary  => .BS

end Calculus
