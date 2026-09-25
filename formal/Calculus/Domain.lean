import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
-- `Finset.sup`, for `Attr.nesting` at `M`: the names are a set, so the layer below is a
-- supremum over the key set and not a fold down a list. `Opaque.lean` imports it for the
-- same reason at `Attr.depth`.
import Mathlib.Data.Finset.Lattice.Fold
/-!
# §1 — The attribute domain

Mechanization of the specification, `docs/blueprint/src/content.tex`. Modelling choices, each recorded where it bites:

* `Numeral` is `String` — the *raw text a parser sees*. The carrier is not: `Attr.n`
  carries `WFNumeral`, the subtype `Numeral.WF` picks out, so `⟨N, "abc"⟩` is
  unrepresentable rather than merely unwritten. The DynamoDB port (`DynamoDB.lean`) gates
  at `Stored`, which is a narrower question than well-formedness.
* Wire sets (`SS`/`NS`/`BS`) are `NEFinset` of a *concrete element type* — `NEFinset
  String`, `NEFinset WFNumeral`, `NEFinset Bytes`, and the same three on `Value`. Maps
  (`M`) are a `Finset Name` with a function on it. Unordered, unique and non-empty are
  properties of the type, so set-ness lives in the carrier and not in §2's `ker p`. The
  kernel's restriction is narrower than it looks: it rejects a `Finset` whose element type
  is the datatype being declared, which is why `union`'s payload is still a list (see
  `Calculus/LiteralArity1.lean`), and accepts one over a concrete type in the same constructor.
* **`N` is carried exactly and this calculus assumes nothing about any numeric type.** The
  value side of `N` is `WFNumeral`, the subtype `Numeral.WF` cuts out, so there is no host
  axiom here at all. A port that hands its own numeric type to a caller adapts that type to
  `WFNumeral` in the port.
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

/-! ## Map payloads

A key *set* with a function on it, which is what `M` is — see `Attr.m` — and what §4's field
table is one stratum up. A `List (Name × α)` admits two orderings of one payload and a repeated
name; both are properties of this type instead.

It sits here rather than beside the codecs because three strata need it and the lowest of them is
the term language: §4's field table is a `MapOf Field`, and `Term.lean` reaches `Domain` and not
`Prisms`. Nothing about it is codec-shaped — a `Finset`, a function, and a lookup. -/

/-- A map's payload: the name set, and the values on it. A dependent pair rather than a
    list of pairs, because that is what `M` is — see `Attr.m`. -/
structure MapOf (α : Type) where
  keys : Finset Name
  get  : {k // k ∈ keys} → α

/-- Two map payloads are equal when their name sets are and their values agree on them.
    The dependent pair needs this said once; the list representation got it from
    `List.ext`. -/
theorem MapOf.ext {α : Type} {p q : MapOf α} (hk : p.1 = q.1)
    (hf : ∀ k (h₁ : k ∈ p.1) (h₂ : k ∈ q.1), p.2 ⟨k, h₁⟩ = q.2 ⟨k, h₂⟩) : p = q := by
  obtain ⟨kp, fp⟩ := p
  obtain ⟨kq, fq⟩ := q
  cases hk
  exact congrArg (MapOf.mk kp) (funext fun k => hf k.1 k.2 k.2)

/-- The value a `MapOf` gives a name, where it gives one — the lookup a key set with a
    function on it has. Generic because the *term*'s field table needs it too. -/
def MapOf.at {α : Type} (m : MapOf α) (k : Name) : Option α :=
  if h : k ∈ m.keys then some (m.get ⟨k, h⟩) else none

/-- A declared name is one the table's key set carries, and conversely. -/
theorem MapOf.at_eq_some {α : Type} {m : MapOf α} {k : Name} {x : α} :
    m.at k = some x ↔ ∃ h : k ∈ m.keys, m.get ⟨k, h⟩ = x := by
  simp only [MapOf.at]
  by_cases h : k ∈ m.1
  · rw [dif_pos h]
    exact ⟨fun he => ⟨h, Option.some.inj he⟩, fun ⟨_, he⟩ => by rw [← he]⟩
  · rw [dif_neg h]
    exact Iff.intro (fun he => nomatch he) (fun ⟨h', _⟩ => absurd h' h)

/-- Every key of the table is declared, at the value the table gives it. -/
theorem MapOf.at_of_mem {α : Type} {m : MapOf α} (k : {k // k ∈ m.1}) :
    m.at k.1 = some (m.2 k) := by
  simp only [MapOf.at, dif_pos k.2]

/-- A property of every value is a property of every declared name's value. -/
theorem MapOf.at_forall {α : Type} {m : MapOf α} {Q : α → Prop}
    (h : ∀ k, Q (m.2 k)) {k x} (hm : m.at k = some x) : Q x := by
  obtain ⟨hk, rfl⟩ := MapOf.at_eq_some.mp hm
  exact h ⟨k, hk⟩


/-! ## §1's `Numerals`

The table in §1 states three clauses: "optional sign, digits, optional point, optional
exponent; ≤ 38 significant digits; magnitude 0 or `1e-130 … 9.9…e125`". All three are
modelled here, as a decidable predicate on the carrier.

`Numeral` stays `String` as the *text* type, and `WFNumeral` — the subtype `WF` cuts out —
is what `Attr.n` carries. So `⟨N, "abc"⟩` is not an attribute at all, and `Carries(N)` in
§1's coproduct is exact rather than approximated. This document argued for a while that the
carrier should stay unrestricted so that a port would see the embedding `⌈·⌉` is partial;
that partiality is a fact about the **port's** types, not the model's, and nothing in the
development ever used an ill-formed `N`.

Note the read side has to check too, not merely the write side. If `p` accepted an
ill-formed numeral it would return a value `e` then refuses, breaking **(C)** — so the
grammar is forced onto both halves by the laws, not by taste.

One narrowing, and it is a narrowing of §1 rather than a transcription of it: a bare integer
part is required, so `".5"` and `"1."` are rejected where DynamoDB *accepts* both and
normalises them (`src/codec/spec/surface/codec.dynamodb.spec.ts`). It stands because `Stored` (`DynamoDB.lean`) rejects them
anyway. Significance is counted between the first and last
nonzero digit, which is the trimming DynamoDB documents.

**`WF` is what DynamoDB accepts; `Stored` is what it hands back.** They are different
sets, and the difference is not cosmetic — see `DynamoDB.lean`. -/

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
  let cs := stripSign s.toList
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

end Numeral

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

/-! **No order is on the set path, and none is needed.** Both sides of every wire set are a
`Finset` of a *concrete element type*: `NEFinset String`, `NEFinset WFNumeral` and `NEFinset Bytes`
on `Value`, the same on `Attr`. So there is no list to sort and no representative to choose.

An order is not excluded by the axiom base. A decidable strict total order on a `Value` with one
generic list-carried set constructor, maps included, proves its three laws on
`[propext, Classical.choice, Quot.sound]` and reaches `Classical.choice` only through routes that
`scripts/classical_gateways.txt` already lists. The kernel refuses the generic carrier that would
not need the order (a nested `Finset`, `Multiset` or `Quot` of the datatype), and the list carrier
needs a canonical spelling that each set codec enforces by refusal, so the carriers are the three
concrete ones. -/

/-- §1's `Numerals` — the strings DynamoDB accepts in an `N`, carried by the type. So
    `Carries(N)` is exact and `⟨N, "abc"⟩` is not an attribute at all.

    The case for leaving the carrier unrefined was that a port should see the embedding `⌈·⌉`
    is partial. That partiality is a fact about the **port's** attribute type, not the
    model's. -/
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

/-! ## §1's nesting bound — the one constraint on `𝔸` the carrier cannot carry

A store can bound how deep the document types nest. The ideal algebra has no such bound, so
the bound is a parameter here, and a port instantiates it: `DynamoDB.maxNesting` is 32.

A subtype `{as : List Attr // Attr.nestingL as ≤ 31}` puts `Attr` under its own declaration
and the kernel refuses it, exactly as it refuses `Finset Attr`. So `Attr` above is the
*unbounded* closure and the bound is stated about it rather than inside it. It was once
recorded as "not typeable" and filed as disposed of on that answer alone; being un-typeable
never made it un-checkable, and `src/` had to gate on it in the end. That failure mode is a
checklist item in `docs/architecture.md`.

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

/-- **§1's `𝔸` as a store with a nesting bound has it.** The `Attr` above is what the calculus
    writes into; this is the subset a store accepts when it nests at most `bound` document
    types. Everything else in §1 is exact, so this predicate is the whole of the difference —
    and `ran(e) ⊆ 𝔸` is only the guarantee it reads as when the two agree. -/
def Attr.Storable (bound : Nat) (a : Attr) : Prop := Attr.nesting a ≤ bound

/-- The value language, partitioned exactly as §5's `Kind`. `decimal` holds numerals as
    `str` values — one string kind, as in the doc's κ table. -/
inductive Value where
  | str  (v : String)
  /-- §1's `N`, carried EXACTLY and as the attribute side already carries it. A host's numeric
      type is an approximation of this and the wire's string is a spelling of it.
      Neither is the datatype, so neither is the carrier: an adapter reaches them. -/
  | num  (v : WFNumeral)
  | bool (v : Bool)
  | bin  (v : Bytes)
  | null
  /-- The reference: "The set types are string set, number set, and binary set." Three
      concrete element types, so each is a genuine `Finset`.

      **These three constructors are DynamoDB facts in the carrier, not rules of the set
      algebra.** The three element types and `℘⁺fin` (no empty set) are the store universe's.
      The algebra is the finite-powerset lift of a lawful element codec (`lawful_setCodec`),
      and the term `set` takes any element term. The one set rule the carrier cannot carry, that
      the element writes one member of `S`, `N` or `B`, is an obligation (`SetElem`). -/
  | strSet (v : NEFinset String)
  | numSet (v : NEFinset WFNumeral)
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
three times over (~~literalOK~~'s `| _ => false`, ~~literalMember~~'s `none`, `literalCodec`'s
`Codec.empty`); `n ≥ 1` and pairwise distinctness were `hne`/`hnd` until `℘⁺fin` typed them;
`ℓᵢ ∈ T` at a base the other constructors could not name was why there were two of them.

`GroundKind` is the premise line as a type. The base is an index, so `member` is a function of
it and `g ground` is unsayable-otherwise; the alternative is one inhabitant of *that base's*
carrier, so `ℓ ⊆ T` is the type. A literal carries one value; several values are a certified
`union` of singletons, and `Calculus/LiteralArity1.lean` derives that rule. -/

/-- The five bases a literal can sit at: `Kind` minus the three container kinds. -/
inductive GroundKind where
  | string | number | boolean | binary | null
deriving DecidableEq, Repr

/-- What each base's held set is drawn from. `Unit` at `.null` is not a degenerate case: `Unit`
    has one inhabitant, so `literal .null` says "exactly null" and cannot say anything else.

    **Reducible**, and that is load-bearing: it lets `Carrier .string` elaborate as `String`, so
    equality at `ℓ` resolves through `String.decEq` and the ordinary instances. An indexed
    `DecidableEq k.Carrier` instance would work too. -/
@[reducible] def GroundKind.Carrier : GroundKind → Type
  | .string  => String
  -- §3's `ℓ ⊆ D` is this base's carrier and not a premise beside it. ~~LiteralD~~ was that
  -- premise and is deleted. `D` IS the well-formed numerals now, so the carrier says so.
  | .number  => WFNumeral
  | .boolean => Bool
  | .binary  => Bytes
  | .null    => Unit

/-- An alternative, as the value it is. Injective at every base. -/
@[simp] def GroundKind.toValue : (k : GroundKind) → k.Carrier → Value
  | .string,  s => .str s
  -- `number` is now the IDENTITY at its carrier: the alternative is already an `N`
  | .number,  x => .num x
  | .boolean, b => .bool b
  | .binary,  b => .bin b
  | .null,    _ => .null

/-- §3 `(literal)`'s member: the one the base stores as. **Total**, and a function of the index
    rather than an index with a premise pinning it — which is the `hμ` the three constructors
    between them carried. -/
@[simp] def GroundKind.member : GroundKind → Member
  | .string  => .S
  | .number  => .N
  | .boolean => .BOOL
  | .binary  => .B
  | .null    => .NULL

/-- §5's `κ` on a literal: the base's kind. -/
@[simp] def GroundKind.kind : GroundKind → Kind
  | .string  => .string
  | .number  => .number
  | .boolean => .boolean
  | .binary  => .binary
  | .null    => .null

/-! ## What a `union` option's admission reads

`Sums.lean` states a union option's admission and cannot see `ObjectSlot`: `Term.lean` is on no
import path below `Calculus.Objects`. So an object option's slot table crosses to `Sums` as
the two things admission reads off each declared name, built in `Denote.lean` where `ObjectSlot` is
in scope. -/

/-- A literal's payload with its base packed in. The value's type depends on the base, so one
    literal as data is this pair and not two fields. -/
abbrev Alts := (k : GroundKind) × k.Carrier

/-- One declared name, as a slice reads it: one presence lattice element, and the value the
    name is pinned to where its field is a literal.

    Each presence pair admits presence and absence, respectively. `alts` is what a clause
    compares against. -/
structure NameSpec where
  presence : Bool × Bool
  alts : Option Alts

end Calculus
