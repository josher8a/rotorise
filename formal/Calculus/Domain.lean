/-!
# §1 — The attribute domain

Mechanization of `docs/codec-calculus.md`. Modelling choices, each recorded where it bites:

* `Numeral` is `String`; the §1 grammar/bounds are a predicate left unmodelled for now.
* Wire sets (`SS`/`NS`/`BS`) and maps (`M`) are lists: a quotient type cannot occur
  recursively inside an inductive, and the laws never inspect order — the quotient of §2
  (`ker p`) is where set-ness lives, not in the carrier.
* `Double` is axiomatized with exactly the shortest-text round trip the doc's `(number)`
  case consumes. That is an IEEE-754 fact, not a theorem of this calculus.
-/

namespace Calculus

/-- Attribute names. -/
abbrev Name := String

/-- Wire numerals (§1 `Numerals`). Well-formedness (grammar, 38 digits, magnitude) is
    an unmodelled predicate for now. -/
abbrev Numeral := String

/-- Byte strings. -/
abbrev Bytes := List UInt8

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
  | ss   (v : List String)
  | ns   (v : List Numeral)
  | bs   (v : List Bytes)
  | l    (v : List Attr)
  | m    (v : List (Name × Attr))

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
  | .m _    => .M

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
  | set  (v : List Value)
  | arr  (v : List Value)
  | map  (v : List (Name × Value))

end Calculus
