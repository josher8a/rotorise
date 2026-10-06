import Calculus.Dynamo.Lang.Term

/-!
# The DynamoDB port

The facts of the store, which the core algebra does not state. The core keeps the general
law: `SurvivesStore c η`, `Codec.Ker` and `Lawful.retract_through_store` hold for every store
normalisation `η`. This module holds the instances at DynamoDB:

* the nesting bound, which the core takes as a parameter of `Attr.Storable`, and `storeCodec`,
  the write gated at the bound;
* `Numeral.Normal` and `Numeral.Stored`, the numerals the store hands back unchanged;
* `decimalCodec`, the codec gated at `Stored`, with its laws and its `SurvivesStore`
  instance, and the refutation that the ungated `baseCodec .number` does not survive the store;
* `numeralOfStoredText` and `textOfNumeral`, the text adapter the host ships as `decimal`.

The ideal algebra has no depth limit. DynamoDB has one, and this module instantiates the
parameter of `Attr.Storable` at the store's number.

`docs/dynamo-datatypes.md:130`: *"The document types are list and map. These data types can
be nested within each other, to represent complex data structures up to 32 levels deep."*
-/

namespace Calculus.DynamoDB

/-- The store's nesting bound. -/
def maxNesting : Nat := 32

end Calculus.DynamoDB

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

/-- The numerals in the form the store hands back. -/
def isStored : Value → Bool :=
  fun v => match v with | .num x => Numeral.Stored x.1 | _ => false

/-- The rule `(decimal)`: the number base restricted to the stored numerals. The restriction checks
    both halves: an ill-formed numeral admitted by `p` would name a value that `e` then refuses,
    and that is **(C)** failing. -/
def decimalCodec : Codec := (baseCodec .number).restrict isStored

theorem carrier_decimalCodec : Carrier decimalCodec :=
  Alg.carrier_restrict (carrier_baseCodec .number) isStored

theorem decimalCodec_e_num (x : WFNumeral) :
    decimalCodec.e (.num x) = if Numeral.Stored x.1 then some (.n x) else none := rfl

theorem decimalCodec_p_n (x : WFNumeral) :
    decimalCodec.p (.n x) = if Numeral.Stored x.1 then some (.num x) else none := rfl

theorem lawful_decimalCodec : Lawful decimalCodec :=
  (lawful_baseCodec .number).restrict isStored

/-! ### `number` against the store

The other side of `decimalCodec`'s answer, and the reason the condition is an inclusion
rather than an equality. -/

/-! **`number` makes no promise about what a normalising store gives back.** `N` is carried
exactly, so `(baseCodec .number).p` is a constructor wrapper. Its kernel is equality, and a store
that rewrites `"1.500"` to `"1.5"` moves the value.

The two numeric terms differ in one thing: `decimal` gates at `Stored`, the store's own
fixpoint, and `survivesStore_decimalCodec` below states that. `number` accepts everything `Numeral.WF`
accepts. -/

/-- `decimal`'s `ker p` is equality — its `p` is the identity on the digits. -/
theorem ker_decimalCodec {x y : WFNumeral} (h : decimalCodec.Ker (.n x) (.n y))
    (hx : Numeral.Stored x.1 = true) : x.1 = y.1 := by
  have h' : decimalCodec.p (.n x) = decimalCodec.p (.n y) := h
  rw [decimalCodec_p_n, decimalCodec_p_n, if_pos hx] at h'
  by_cases hy : Numeral.Stored y.1 = true
  · rw [if_pos hy] at h'
    exact congrArg Subtype.val (Attr.n.inj (Option.some.inj h'))
  · rw [if_neg hy] at h'; exact nomatch h'

/-- `Can(decimal)` is the normal forms and a normalisation fixes its own, so `Stored`
    discharges `η ⊆ ker p`. Necessity is `not_survivesStore_numberCodec`. -/
theorem survivesStore_decimalCodec {η : Attr → Attr}
    (hη : ∀ s : WFNumeral, Numeral.Stored s.1 = true → η (.n s) = .n s) :
    SurvivesStore decimalCodec η := by
  rintro a ⟨v, hv⟩
  cases v with
  | n x =>
    rw [decimalCodec_e_num] at hv
    by_cases hs : Numeral.Stored x.1 = true
    · rw [if_pos hs] at hv
      cases hv
      show decimalCodec.p (η (.n x)) = decimalCodec.p (.n x)
      rw [hη x hs]
    · rw [if_neg hs] at hv; exact nomatch hv
  | _ => exact nomatch hv

/-! ## The numeral domain `Numerals`, checked

`Domain.lean` carries the predicate `Numeral.WF`, with the grammar, the 38 significant digits and the
magnitude range, and `decimalCodec` gates on it. `typed_e_mem` reports whether the codec
respects the predicate, so here is that report.

The carrier is not unrestricted either: `Attr.n` carries `WFNumeral`, so `⟨N, "abc"⟩` is not
an attribute and `decimal`'s report below is about a codec whose target is exactly the numeral domain. That
a port sees the embedding as partial is a fact about the port's types, not the model's. -/

/-- `decimal`'s held set is exactly `Numerals`. -/
theorem decimal_T (v : Value) :
    decimalCodec.T v ↔ ∃ x : WFNumeral, v = .num x ∧ Numeral.Stored x.1 = true := by
  constructor
  · rintro ⟨hm, h⟩; cases v <;> first | exact ⟨_, rfl, h⟩ | exact nomatch hm
  · rintro ⟨x, rfl, h⟩; exact ⟨rfl, h⟩

/-- **The report.** `decimalCodec` writes only well-formed numerals — the
    `: T` index, cashed on the attribute side. -/
theorem decimal_writes_stored {v : Value} {a : Attr}
    (he : decimalCodec.e v = some a) :
    ∃ x : WFNumeral, a = .n x ∧ Numeral.Stored x.1 = true := by
  cases v with
  | n x =>
    rw [decimalCodec_e_num] at he
    by_cases hw : Numeral.Stored x.1 = true
    · rw [if_pos hw] at he; cases he; exact ⟨_, rfl, hw⟩
    · rw [if_neg hw] at he; exact nomatch he
  | _ =>
    replace he : (none : Option Attr) = some a := he
    exact nomatch he

/-- Dually, it reads only well-formed numerals — which is not a nicety: a `p` accepting an
    ill-formed `N` would name a value `e` then refuses, and that is **(C)** failing. -/
theorem decimal_reads_stored {a : Attr} {v : Value}
    (hp : decimalCodec.p a = some v) :
    ∃ x : WFNumeral, a = .n x ∧ Numeral.Stored x.1 = true := by
  cases a with
  | n x =>
    replace hp : (if Numeral.Stored x.1 = true then some (Value.num x) else none) = some v := hp
    by_cases hw : Numeral.Stored x.1 = true
    · exact ⟨x, rfl, hw⟩
    · rw [if_neg hw] at hp; exact nomatch hp
  | _ =>
    replace hp : (none : Option Value) = some v := hp
    exact nomatch hp

/-! ### The gate at the store

`decimal` writes an `N` only for a numeral the store hands back unchanged. No reading of the
specification produces that gate, because it is a fact about the **store** rather than about
the calculus.

`"1e+21"` is well formed, and a check that puts it out of range
is a defect: the bound that bites is magnitude rather than notation. That is
true of `Numeral.WF`, which is what DynamoDB *accepts*. It is not true of `decimal`,
because DynamoDB hands `1e+21` back as `1000000000000000000000`, and `decimal`'s `p` is the
identity on the digits — so the round trip fails at the one point the codec laws cannot see, between
`e` and `p`. `Numeral.Stored` is that set, and the measurements it is read off are in
`src/codec/spec/surface/codec.dynamodb.spec.ts`. -/

theorem decimal_refuses_nonNumeral : decimalCodec.e (.str "abc") = none := rfl

/-- Magnitude, isolated at the `WF` level, where notation is not also in play. -/
theorem wf_refuses_overMagnitude : Numeral.WF "1e130" = false := by decide

theorem wf_refuses_39_digits :
    Numeral.WF "123456789012345678901234567890123456789" = false := by decide

theorem decimal_refuses_39_digits :
    decimalCodec.e (.str "123456789012345678901234567890123456789") = none := rfl

/-- The service accepts an exponent: `"1e+21"` is well formed. -/
theorem wf_accepts_exponent : Numeral.WF "1e+21" = true := by decide

/-- `decimal` does not, and the reason is the store rather than the grammar. -/
theorem decimal_refuses_exponent :
    decimalCodec.e (.num (.of "1e+21")) = none := rfl

/-- The same number, spelled the way it comes back. -/
theorem decimal_accepts_expanded :
    decimalCodec.e (.num (.of "1000000000000000000000"))
      = some (.n (.of "1000000000000000000000")) := rfl

/-! ## `decimalCodec` without its narrowed held set

`survivesStore_decimalCodec` shows that gating on `Numeral.Stored` discharges `η ⊆ ker p`.
This is the other half: the codec that gates on `Numeral.WF` instead — the *whole* numeral
grammar — does not, and the witness is a form
DynamoDB was measured to normalise.

Without this the narrowing reads as a precaution. With it, it is the only option: `WF` admits
`"1.500"`, the store returns `"1.5"`, `decimal`'s `ker p` is equality (`ker_decimalCodec`),
and (R) through the store fails on a value the codec claimed to hold. -/

/-! `decimal`, gated on the numeral grammar rather than on what the store hands back — which is
    **`baseCodec .number`, the base `decimal` actually refines**. Since `Attr.n` carries
    `WF`, there is no wider text-side numeric codec to invent, so this refutation says
    something about the base itself rather than about a codec built for the purpose.

    Note its read is *total*: `WF` is the carrier, so a gate on `p` has nothing to reject. That is the whole asymmetry `decimal` adds — `Stored` is a
    strictly smaller set than `WF`, and only the smaller one survives the store. -/

/-- `"1.500"` is one of the forms `stored_rejects_denormal` records the store rewriting, and
    the un-narrowed codec claims to hold it. -/
theorem can_numberCodec_denormal : Can (baseCodec .number) (.n (.of "1.500")) :=
  ⟨.num (.of "1.500"), by rw [baseCodec_e_num]⟩

/-- **The un-narrowed `decimal` does not survive the store.** Any `η` that normalises
    `"1.500"` — which is what DynamoDB was measured to do — falls outside its `ker p`. -/
theorem not_survivesStore_numberCodec {η : Attr → Attr}
    (hη : η (.n (.of "1.500")) = .n (.of "1.5")) : ¬ SurvivesStore (baseCodec .number) η := by
  intro h
  have hk : (baseCodec .number).p (η (.n (.of "1.500"))) = (baseCodec .number).p (.n (.of "1.500")) :=
    h _ can_numberCodec_denormal
  rw [hη, baseCodec_p_n, baseCodec_p_n] at hk
  exact absurd (congrArg Subtype.val (Attr.n.inj (Option.some.inj hk))) (by decide)

/-- And (R) through the store fails outright: the value is written, the store rewrites the
    attribute, and the codec reads back something else — the shape of the shipped defect. -/
theorem not_retract_through_store_numberCodec {η : Attr → Attr}
    (hη : η (.n (.of "1.500")) = .n (.of "1.5")) :
    (baseCodec .number).e (.num (.of "1.500")) = some (.n (.of "1.500")) ∧
      (baseCodec .number).p (η (.n (.of "1.500"))) ≠ some (.num (.of "1.500")) := by
  refine ⟨by rw [baseCodec_e_num], ?_⟩
  rw [hη, baseCodec_p_n]
  intro hk
  exact absurd (congrArg Subtype.val (Attr.n.inj (Option.some.inj hk))) (by decide)

/-! ## The write the store holds

`Attr.l` and `Attr.m` nest without limit, so a lawful codec can write an attribute past
`maxNesting`. `storeCodec` gates the stored side at the bound. The gate reads the written
attribute, not the value: a set write has nesting one less than the value it writes. A gate on
the write alone breaks **(C)**, because a read past the bound then names a value that the write
refuses. `refine2` gates both halves, so the laws hold over the gate with no premise.
-/

/-- The attributes that the store holds: nesting at most `DynamoDB.maxNesting`. -/
def isStorable (a : Attr) : Bool := decide (Attr.nesting a ≤ DynamoDB.maxNesting)

/-- **The DynamoDB write**: `c` with its stored side gated at the nesting bound. -/
def storeCodec (c : Codec) : Codec := Alg.refine2 c (fun _ => true) isStorable

/-- The gate keeps the laws, and owes no premise. -/
theorem lawful_storeCodec {c : Codec} (h : Lawful c) : Lawful (storeCodec c) :=
  h.refine2 _ _

/-- The gate keeps the carrier. -/
theorem carrier_storeCodec {c : Codec} (h : Carrier c) : Carrier (storeCodec c) :=
  Alg.carrier_refine2 h _ _

/-- **The store codec writes only what the store holds.** -/
theorem storeCodec_storable (c : Codec) {v a} (he : (storeCodec c).e v = some a) :
    Attr.Storable DynamoDB.maxNesting a :=
  (of_decide_eq_true ((Alg.refine2_f.mp he).2.2 : isStorable a = true) :
    Attr.nesting a ≤ DynamoDB.maxNesting)

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

/-- `decimal`, as the surface ships it: the numeric base under the text adapter, with the
    caller side restricted to text. -/
def decimalHeld : Term := Term.held false Term.number Term.string (.decimalText, false) []

end Calculus
