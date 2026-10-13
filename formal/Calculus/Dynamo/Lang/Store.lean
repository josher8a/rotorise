import Calculus.Dynamo.Lang.Term
import Calculus.Dynamo.Lang.Adapters

/-!
# The DynamoDB port

The facts of the store, which the core algebra does not state. The core keeps the general
law: `SurvivesStore c η`, `Codec.Ker` and `Lawful.retract_through_store` hold for every store
normalisation `η`. This module holds the instances at DynamoDB:

* the nesting bound, which the core takes as a parameter of `Attr.Storable`, and `storeCodec`,
  the write gated at the bound and at the stored numerals;
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
magnitude range, and `decimalCodec` gates on it. `Closed.carrier` reports whether a codec
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
`maxNesting`. The store also returns each numeral in its stored form, at every depth: an `N`, each
element of an `NS`, and each numeral inside an `L` or an `M`. `storeCodec` gates the stored side
at the bound and at the stored numerals. The gate reads the written attribute, not the value: a
set write has nesting one less than the value it writes. A gate on the write alone breaks **(C)**,
because a read outside the gate then names a value that the write refuses. `refine2` gates both
halves, so the laws hold over the gate with no premise.
-/

mutual

/-- Each numeral in the attribute is `Numeral.Stored`: an `N`, each element of an `NS`, and each
    numeral inside an `L` or an `M`. -/
def Attr.numeralsStored : Attr → Bool
  | .n x => Numeral.Stored x.1
  | .ns xs => decide (∀ x ∈ xs.1, Numeral.Stored x.1 = true)
  | .s _ | .b _ | .bool _ | .null | .ss _ | .bs _ => true
  | .l as => Attr.numeralsStoredL as
  | .m keys f => decide (∀ k ∈ keys.attach, Attr.numeralsStored (f k) = true)

/-- The list mirror that `Attr.numeralsStored` needs at `L`. -/
def Attr.numeralsStoredL : List Attr → Bool
  | [] => true
  | a :: as => Attr.numeralsStored a && Attr.numeralsStoredL as

end

/-- The attributes that the store holds: nesting at most `DynamoDB.maxNesting`, and each numeral
    in the stored form. -/
def isStorable (a : Attr) : Bool :=
  decide (Attr.nesting a ≤ DynamoDB.maxNesting) && Attr.numeralsStored a

/-- **The DynamoDB write**: `c` with its stored side gated at `isStorable`. -/
def storeCodec (c : Codec) : Codec := Alg.refine2 c (fun _ => true) isStorable

/-- The gate keeps the laws, and owes no premise. -/
theorem lawful_storeCodec {c : Codec} (h : Lawful c) : Lawful (storeCodec c) :=
  h.refine2 _ _

/-- The gate keeps the carrier. -/
theorem carrier_storeCodec {c : Codec} (h : Carrier c) : Carrier (storeCodec c) :=
  Alg.carrier_refine2 h _ _

/-- **The store codec writes only what the store holds**: the nesting is within the bound, and
    each numeral is in the stored form. -/
theorem storeCodec_storable (c : Codec) {v a} (he : (storeCodec c).e v = some a) :
    Attr.Storable DynamoDB.maxNesting a ∧ Attr.numeralsStored a = true :=
  have h := (Bool.and_eq_true _ _).mp ((Alg.refine2_f.mp he).2.2 : isStorable a = true)
  ⟨(of_decide_eq_true h.1 : Attr.nesting a ≤ DynamoDB.maxNesting), h.2⟩

/-- **The port refuses a numeral that the store rewrites**: the store returns `"1.500"` as
    `"1.5"`. -/
theorem storeCodec_refuses_denormal :
    (storeCodec (baseCodec .number)).e (.num (.of "1.500")) = none := rfl

/-- …and writes the stored form unchanged. -/
theorem storeCodec_writes_stored :
    (storeCodec (baseCodec .number)).e (.num (.of "1.5")) = some (.n (.of "1.5")) := rfl

end Calculus
