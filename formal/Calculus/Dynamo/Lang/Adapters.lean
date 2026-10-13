import Calculus.Dynamo.Lang.Term

/-!
# The numerals of the store, and the adapters of the library

The store hands back a numeral in a normal spelling (`Numeral.Stored`). The text adapter of the
library reads that spelling (`numeralOfStoredText`), and `libTable` gives the adapter of each
generator: the text adapter, or the pair that a caller supplies.
-/

namespace Calculus

namespace Numeral

/-! ### What the store hands back

The codec laws compose a codec's `e` and `p` directly. In use there is a **store** between them, and
it is not the identity on attributes: DynamoDB normalises every `N` it accepts — trimming
leading and trailing zeros, dropping `+`, expanding exponents, and keeping one spelling of
zero. Measured rather than assumed: `src/codec/spec/surface/codec.dynamodb.spec.ts` puts each of these forms into a
real table and reads it back, and the two theorems below are that measurement.

Write `η` for the store's normalisation. A codec survives the round trip through the store
exactly when **`η` lies inside `ker p`** — the codec equivalence `≈c`, the relation that already exists for
"a different attribute that reads to the same value". `number` satisfies it for free:
`p "1.500"` and `p "1.5"` are the same double. `decimal` cannot, because its `p` is the
identity on the digits, so `ker p` is equality and `η` would have to be too.

So `decimal`'s held set is not `Numerals`. It is the numerals the store returns unchanged,
and that is what this predicate is.

`η ⊆ ker p` is not only prose. `Codec.Ker` names the codec equivalence `≈c` and `SurvivesStore` names
the inclusion, both in `Codec.lean`; `Lawful.retract_through_store` is what they buy, which
is **(R)** with the store in the middle. The two halves for `decimal` are
`survivesStore_decimalCodec` — the narrowing discharges the premise, because a normalisation
fixes its own normal forms — and `not_survivesStore_numberCodec` below, which
is the codec that gates on `WF` instead, failing on `"1.500"`. `ker_decimalCodec` is the fact
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
  match s.toList with
  | '-' :: cs => normalMag cs && !(cs == ['0'])
  | cs => normalMag cs

/-- `decimal`'s held set: accepted *and* returned unchanged. -/
def Stored (s : Numeral) : Bool := WF s && Normal s

/-- What the store hands back, it also accepts — so a `Stored` numeral is a `WFNumeral`
    without further checking. `decimal` needs this because `Attr.n` carries the proof. -/
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

/-! ## The adapters this library ships, named so a vector can cite them

`src/codec/lean.ts` prints `held` with the generator `decimalText` for the adapter it recognises,
the way it already prints a predicate it ships as `Numeral.WF` or `Numeral.Stored`. `number` and
`decimal` are adapters over the one numeric base on that surface, so the pair of each needs a name
here, or no vector at that base can be stated at all. `libTable` gives the named pair to the
generator.

**The text adapter only.** A caller holding a JS float has no adapter here and cannot have one:
`Value` carries no float, so the conversion would be numeral to numeral and its content is
binary64 rounding. Writing that down needs a host axiom that this development does not assert, so
the emitter refuses a float-carrying codec by name instead.
-/

/-- **Text in, numeral out**, gated where `decimal` gates: the spelling the store returns.

    Total, as `held` requires. Text the gate turns down is left where it is, and the base then
    refuses it, which is how a partial conversion is written in a language whose adapters are
    total. -/
def numeralOfStoredText : Value → Value := fun v =>
  match v with
  | .str s =>
      if h : Numeral.WF s = true then
        if Numeral.Stored s then Value.num ⟨s, h⟩ else Value.null
      else Value.null
  -- the caller holds TEXT, so anything else is not a value this adapter carries, and the
  -- base refuses what it is handed. `null` is the one constructor `number` never admits
  | _ => Value.null

/-- …and back, which is the numeral's own digits. -/
def textOfNumeral : Value → Value := fun v =>
  match v with
  | .num x => Value.str x.1
  | _ => v

/-- **The adapters of the callers**: the two functions of the `n`th adapter that a caller
    supplies. -/
abbrev Callers : Type := Nat → (Value → Value) × (Value → Value)

/-- **The table of the library**: `decimalText` is the text adapter, and a caller generator
    reads the pair that the caller supplies. -/
def libTable (κ : Callers) : Table
  | .decimalText => (numeralOfStoredText, textOfNumeral)
  | .caller n => κ n

/-- **The caller table of a term with no caller adapter.** A vector that states a value states
    it at a term that holds no caller generator, so no entry of this table is read. -/
def noCallers : Callers := fun _ => (id, id)

end Calculus
