import Calculus.Lists
import Calculus.Codec

/-!
# Constructors as prisms, the ground codecs and the wrappers

The entry point of the certified combinator algebra: the semantic constructions the
denotation factors through, each carrying its own lawfulness lemma, so soundness becomes
plumbing rather than twenty-one bespoke cases.

* `Ctor` — a constructor as a prism, on the value side and the attribute side;
* ground codecs, one per §3 ground term;
* `through` / `restrict` — the iso/prism pair behind `held` and `refine`;
* `extendRead` — the agreeing extension of the reading, for `legacy`; (MP) is the
  sanctioned breach and has no lemma, by design;
* `orNull` — `nullable`, whose honesty premises are (U) for a two-option sum.
-/

namespace Calculus

noncomputable section

/-! ## Constructors as prisms

The shape this file is built out of. A constructor viewed as a partial iso onto its image
is the prism §7 of the specification already names when it calls `held` and `refine` "the
same shape at different strengths". Two families turn out to be instances, and each was
written out once per constructor before it was named:

* the **point ground codecs** (`pointCodec` below) — `string`, `boolean`, `binary` and
  `null` are a payload carried between a value constructor and an attribute constructor,
  differing in nothing but which pair;
* the **scalar payload prisms** (`sC`/`nC`/`bC`) — the attribute half of three of those
  pairs, factored out because `encSet` needs the same three prisms to decide which wire set
  a homogeneous element set writes to.

Naming the shape once is what lets §2's four laws be discharged once for each family
rather than once per constructor. -/

/-- A constructor, as a partial iso onto its image. -/
structure Ctor (α β : Type) where
  /-- Build. -/
  into : α → β
  /-- Match, partially. -/
  out : β → Option α
  /-- Matching what was built returns it. -/
  out_into : ∀ x, out (into x) = some x
  /-- Anything that matches was built. -/
  into_out : ∀ {b x}, out b = some x → b = into x

/-! ### The prisms, value side and attribute side -/

/-- `str` values. -/ def strV : Ctor String Value where
  into := Value.str
  out := fun v => match v with | .str s => some s | _ => none
  out_into _ := rfl
  into_out {b x} h := by cases b <;> first | (cases h; rfl) | exact nomatch h

/-- `bool` values. -/ def boolV : Ctor Bool Value where
  into := Value.bool
  out := fun v => match v with | .bool b => some b | _ => none
  out_into _ := rfl
  into_out {b x} h := by cases b <;> first | (cases h; rfl) | exact nomatch h

/-- `bin` values. -/ def binV : Ctor Bytes Value where
  into := Value.bin
  out := fun v => match v with | .bin b => some b | _ => none
  out_into _ := rfl
  into_out {b x} h := by cases b <;> first | (cases h; rfl) | exact nomatch h

/-- The `null` *point*: a prism with a trivial payload, which is what makes `null` an
    instance of the same shape as the three that carry data. -/
def nullV : Ctor Unit Value where
  into := fun _ => .null
  out := fun v => match v with | .null => some () | _ => none
  out_into _ := rfl
  into_out {b x} h := by cases b <;> first | (cases h; rfl) | exact nomatch h

/-- `S`'s payload. -/ def sC : Ctor String Attr where
  into := Attr.s
  out := fun a => match a with | .s v => some v | _ => none
  out_into _ := rfl
  into_out {b x} h := by cases b <;> first | (cases h; rfl) | exact nomatch h

/-- `N`'s payload. -/ def nC : Ctor WFNumeral Attr where
  into := Attr.n
  out := fun a => match a with | .n v => some v | _ => none
  out_into _ := rfl
  into_out {b x} h := by cases b <;> first | (cases h; rfl) | exact nomatch h

/-- `B`'s payload. -/ def bC : Ctor Bytes Attr where
  into := Attr.b
  out := fun a => match a with | .b v => some v | _ => none
  out_into _ := rfl
  into_out {b x} h := by cases b <;> first | (cases h; rfl) | exact nomatch h

/-- `BOOL`'s payload. -/ def boolA : Ctor Bool Attr where
  into := Attr.bool
  out := fun a => match a with | .bool v => some v | _ => none
  out_into _ := rfl
  into_out {b x} h := by cases b <;> first | (cases h; rfl) | exact nomatch h

/-- `NULL`'s point. -/ def nullA : Ctor Unit Attr where
  into := fun _ => .null
  out := fun a => match a with | .null => some () | _ => none
  out_into _ := rfl
  into_out {b x} h := by cases b <;> first | (cases h; rfl) | exact nomatch h

/-! ### The container prisms

The same shape one level up: a constructor whose payload is a *list* of entries. `L` and
`M` are the two §1 provides on the attribute side, `arr` and `map` the two §3 writes into
them. Naming them is what lets `array` and `record` be one construction (`entrywise`,
under Products) rather than two. -/

/-- `arr` values. -/ def arrV : Ctor (List Value) Value where
  into := Value.arr
  out := fun v => match v with | .arr xs => some xs | _ => none
  out_into _ := rfl
  into_out {b x} h := by cases b <;> first | (cases h; rfl) | exact nomatch h

/-- `map` values. -/ def mapV : Ctor (MapOf Value) Value where
  into := fun p => Value.map p.1 p.2
  out := fun v => match v with | .map keys f => some ⟨keys, f⟩ | _ => none
  out_into _ := rfl
  into_out {b x} h := by cases b <;> first | (cases h; rfl) | exact nomatch h

/-- `L`'s payload. -/ def lA : Ctor (List Attr) Attr where
  into := Attr.l
  out := fun a => match a with | .l xs => some xs | _ => none
  out_into _ := rfl
  into_out {b x} h := by cases b <;> first | (cases h; rfl) | exact nomatch h

/-- `M`'s payload. -/ def mA : Ctor (MapOf Attr) Attr where
  into := fun p => Attr.m p.1 p.2
  out := fun a => match a with | .m keys f => some ⟨keys, f⟩ | _ => none
  out_into _ := rfl
  into_out {b x} h := by cases b <;> first | (cases h; rfl) | exact nomatch h

/-- **The map analogue of `setImage`, and much simpler.** A set codec can collide two
    elements onto one; a map cannot, because the names are fixed and the codec only moves
    the values. So all this has to do is demand that every value succeeds. -/
noncomputable def funImage {β : Type} {keys : Finset Name}
    (g : {k // k ∈ keys} → Option β) : Option ({k // k ∈ keys} → β) :=
  if h : ∀ k, (g k).isSome = true then some (fun k => (g k).get (h k)) else none

theorem funImage_some {β : Type} {keys : Finset Name} {g : {k // k ∈ keys} → Option β}
    {f : {k // k ∈ keys} → β} (h : funImage g = some f) : ∀ k, g k = some (f k) := by
  unfold funImage at h
  split at h
  · next hall =>
      intro k
      have := Option.some.inj h
      subst this
      exact (Option.some_get (hall k)).symm
  · exact nomatch h

theorem funImage_isSome {β : Type} {keys : Finset Name} {g : {k // k ∈ keys} → Option β}
    (hall : ∀ k, (g k).isSome = true) : (funImage g).isSome = true := by
  unfold funImage; rw [dif_pos hall]; rfl

/-- …and exactly when, which is what the exactness rows need: `funImage` is defined at a
    key set precisely where every entry is. -/
theorem funImage_isSome_iff {β : Type} {keys : Finset Name}
    {g : {k // k ∈ keys} → Option β} :
    (funImage g).isSome = true ↔ ∀ k, (g k).isSome = true := by
  refine ⟨fun h k => ?_, funImage_isSome⟩
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp h
  rw [funImage_some hf k]; rfl

theorem funImage_map_isSome {β γ : Type} {keys : Finset Name}
    {g : {k // k ∈ keys} → Option β} (h : (funImage g).isSome = true)
    (f : ({k // k ∈ keys} → β) → γ) : ((funImage g).map f).isSome = true := by
  cases hh : funImage g with
  | none => rw [hh] at h; exact absurd h (by simp)
  | some x => simp

theorem funImage_eq {β : Type} {keys : Finset Name} {g : {k // k ∈ keys} → Option β}
    {f : {k // k ∈ keys} → β} (h : ∀ k, g k = some (f k)) : funImage g = some f := by
  unfold funImage
  rw [dif_pos (fun k => by rw [h k]; rfl)]
  congr 1
  funext k
  exact Option.some.inj ((Option.some_get _).trans (h k))

/-- **The point ground codecs of §3**, as one construction: a payload carried between a
    value constructor and an attribute constructor, both prisms.

    The prism laws are exactly §2's laws in disguise — `out_into` is the round trip **(R)**
    and `into_out` is canonizability **(C)** — which is why `lawful_pointCodec` needs no
    hypothesis about either side beyond the member it stamps. -/
def pointCodec {α : Type} (V : Ctor α Value) (A : Ctor α Attr) (μ₀ : Member) : Codec :=
  { T := fun v => ∃ x, v = V.into x
    μ := some μ₀
    e := fun v => (V.out v).map A.into
    p := fun a => (A.out a).map V.into }

/-! ## Ground codecs (§3) -/

def stringCodec : Codec :=
  { T := fun v => ∃ s, v = .str s
    μ := some .S
    e := fun v => match v with | .str s => some (.s s) | _ => none
    p := fun a => match a with | .s s => some (.str s) | _ => none }

/-- §3 `(number)`. The held set is `D` — §1's numeral domain — not every double.

    `p` gates on the **round-tripped** value rather than on the stored digits: `ofDec` rounds,
    and a numeral at the top of the range can round *up* past it, so gating on `x` would admit
    a double `e` then refuses — **(C)** failing.

    Whether any double is outside `D` is an IEEE-754 fact the model declines to assert. -/
def numberCodec : Codec :=
  { T := fun v => ∃ d, v = .num d ∧ Numeral.WF d.toDec = true
    μ := some .N
    e := fun v => match v with
      -- The `dite` is where the proof `Attr.n` demands is produced. The check was
      -- already here; it used to be made and thrown away.
      | .num d => if h : Numeral.WF d.toDec then some (.n ⟨d.toDec, h⟩) else none
      | _ => none
    p := fun a => match a with
      | .n x => (Double.ofDec x.1).bind fun d =>
          if Numeral.WF d.toDec then some (.num d) else none
      | _ => none }

theorem numberCodec_e_num (d : Double) :
    numberCodec.e (.num d)
      = if h : Numeral.WF d.toDec then some (.n ⟨d.toDec, h⟩) else none := rfl

theorem numberCodec_p_n (x : WFNumeral) :
    numberCodec.p (.n x) =
      (Double.ofDec x.1).bind (fun d => if Numeral.WF d.toDec then some (.num d) else none) :=
  rfl

/-- §3 `(decimal)`. The held set is §1's `Numerals`, not every string: the grammar, the
    38 significant digits and the magnitude range are checked on both halves. The read
    side has to check as well — an ill-formed numeral admitted by `p` would name a value
    `e` then refuses, and that is **(C)** failing. -/
def decimalCodec : Codec :=
  { T := fun v => ∃ s, v = .str s ∧ Numeral.Stored s = true
    μ := some .N
    e := fun v => match v with
      | .str s => if h : Numeral.Stored s then some (.n ⟨s, Numeral.stored_wf h⟩) else none
      | _ => none
    p := fun a => match a with
      | .n x => if Numeral.Stored x.1 then some (.str x.1) else none
      | _ => none }

def booleanCodec : Codec :=
  { T := fun v => ∃ b, v = .bool b
    μ := some .BOOL
    e := fun v => match v with | .bool b => some (.bool b) | _ => none
    p := fun a => match a with | .bool b => some (.bool b) | _ => none }

def binaryCodec : Codec :=
  { T := fun v => ∃ b, v = .bin b
    μ := some .B
    e := fun v => match v with | .bin b => some (.b b) | _ => none
    p := fun a => match a with | .b b => some (.bin b) | _ => none }

/-- The `NULL` point: one value, one attribute. A building block of `opaqCodec`. -/
def nullCodec : Codec :=
  { T := fun v => v = .null
    μ := some .NULL
    e := fun v => match v with | .null => some .null | _ => none
    p := fun a => match a with | .null => some .null | _ => none }

/-- The pair a literal refines: its base's, chosen by the index.

    §3's `(literal)` premise is `⊢ g : T ⇝ μ, g ground`, and this is `g`. It exists because
    the rule quantifies over the base — the three constructors this replaces had it hard-coded
    three times over, which is why `literal-S` and `literal-N` were two rules and `boolean`,
    `binary` and `null` were none. -/
noncomputable def baseCodec : GroundKind → Codec
  | .string  => stringCodec
  | .number  => numberCodec
  | .decimal => decimalCodec
  | .boolean => booleanCodec
  | .binary  => binaryCodec
  | .null    => nullCodec

/-- §3 `(set)`'s element pair, chosen by the base.

    `denote (.set b)` is `setCodec b.elem`, which is why `setCodec`, `encSet`, `decSet` and
    `setImage` are untouched by the re-indexing: the *constructor* changed, the combinator
    did not. Four bases, three wire members — `decimal` and `number` are both `NS`, and are
    different pairs at it. -/
noncomputable def SetBase.elem : SetBase → Codec
  | .string  => stringCodec
  | .number  => numberCodec
  | .decimal => decimalCodec
  | .binary  => binaryCodec

/-- `literal(ℓ)`'s predicate: the value is one of the alternatives.

    One definition where there were two (~~inLS~~, ~~inLN~~) and three bases with none. Dispatching
    on the index first is what makes the carrier concrete, and so the membership decidable. -/
noncomputable def inL : (k : GroundKind) → NEFinset k.Carrier → Value → Bool
  | .string,  ls, .str s  => decide (s ∈ ls.1)
  -- `number`'s carrier is gated too now (`WFDouble`), so this row is `decimal`'s: membership
  -- goes *through* the gate, and a double whose text §1 refuses is in no alternative set.
  | .number,  ls, .num d  =>
      if h : Numeral.WF d.toDec = true then decide ((⟨d, h⟩ : WFDouble) ∈ ls.1) else false
  -- `decimal`'s value is a `.str` and its carrier is the `Stored` subtype, so membership goes
  -- through the gate rather than round it: a text that is not stored is in no alternative set.
  | .decimal, ls, .str s  =>
      if h : Numeral.Stored s = true then decide ((⟨s, h⟩ : StoredNumeral) ∈ ls.1) else false
  | .boolean, ls, .bool b => decide (b ∈ ls.1)
  | .binary,  ls, .bin b  => decide (b ∈ ls.1)
  | .null,    _,  .null   => true
  | _, _, _ => false

/-! `inL`'s rows at the four ungated bases, as `@[simp]` equations.

Without these a `simp` that needs `inL` at one base unfolds `inL.match_1` — the matcher Lean
derives for the whole ten-row table — and pays for all ten rows at every rewrite. That is what
~~fanOf~~ found behind `AdmA_exact`'s duplication. `number` and `decimal` get no equation here:
their rows are a `dite` on a gate, so the useful statement is about the gate rather than about
the row, and `hLit_of_inL`'s two `cases hs :` branches are where that is done. -/

/-- `.str` at `string`: the payload *is* the carrier, so this is `rfl`. -/
@[simp] theorem inL_str (ls : NEFinset String) (s : String) :
    inL .string ls (.str s) = decide (s ∈ ls.1) := rfl

/-- `.bool` at `boolean`, on the same terms. -/
@[simp] theorem inL_bool (ls : NEFinset Bool) (b : Bool) :
    inL .boolean ls (.bool b) = decide (b ∈ ls.1) := rfl

/-- `.bin` at `binary`, on the same terms. -/
@[simp] theorem inL_bin (ls : NEFinset Bytes) (b : Bytes) :
    inL .binary ls (.bin b) = decide (b ∈ ls.1) := rfl

/-- `.null` at `null`: the alternative set cannot distinguish anything, `Unit` having one
    inhabitant and `℘⁺fin` no empty one, so the row is `true` and not a membership test. -/
@[simp] theorem inL_null (ls : NEFinset Unit) :
    inL .null ls .null = true := rfl

/-- §3's `{ℓ₁ … ℓₙ}` — the held set, uniform in the base because `toValue` is. Spelled
    `Value → Prop` rather than `Held`, which is `Typing`'s abbreviation and one module down. -/
def HLit (k : GroundKind) (ls : NEFinset k.Carrier) : Value → Prop :=
  fun v => ∃ x, x ∈ ls.1 ∧ v = k.toValue x


/-! ## Wrappers -/

/-- `held`: an iso on the value side; the stored side is untouched. -/
def Codec.through (c : Codec) (f g : Value → Value) : Codec :=
  { T := fun v => c.T (f v)
    μ := c.μ
    e := fun v => c.e (f v)
    p := fun a => (c.p a).map g }

/-- `refine`: the prism. -/
def Codec.restrict (c : Codec) (q : Value → Bool) : Codec :=
  { T := fun v => c.T v ∧ q v
    μ := c.μ
    e := fun v => if q v then c.e v else none
    p := fun a => (c.p a).bind fun v => if q v then some v else none }

/-- **The combinator `held` and `refine` both are.** A partial iso either side of the
    pair: `f` in front of the writing, `g` behind the reading, both allowed to refuse.

    §3 keeps the two apart and says why — "the literature collapses them … which is
    exactly the merged combinator", separated for a reason *outside* the calculus, since a
    total `g` lets a generator for `I` be pushed forward while a partial one leaves only
    rejection sampling. This is that merged combinator, so the claim is checked rather
    than asserted: `through` is `adapt` with both halves total, `refine` is `adapt` with a
    partial identity on both halves, and the four theorems below are the whole of it.

    The `Codec` is not redefined in its terms. `T` agrees only propositionally — `adapt`'s
    is `∃ w, f v = some w ∧ c.T w` where `through`'s is `c.T (f v)` — so a merge at the
    definition would cost every `rfl` over the two wrappers, which is the trade `withNull`
    already showed is not worth taking blind. The pair is what the claim is about, and the
    pair agrees on the nose. -/
def Codec.adapt (c : Codec) (f g : Value → Option Value) : Codec :=
  { T := fun v => ∃ w, f v = some w ∧ c.T w
    μ := c.μ
    e := fun v => (f v).bind c.e
    p := fun a => (c.p a).bind g }

/-- The partial identity on a predicate — `refine`'s adapter, on both halves. -/
def partialId (q : Value → Bool) : Value → Option Value := fun v => if q v then some v else none

/-- `held` writes as `adapt` with a total adapter. -/
theorem through_e_adapt {c : Codec} (f g : Value → Value) :
    (c.through f g).e = (c.adapt (some ∘ f) (some ∘ g)).e := rfl

/-- …and reads as one. -/
theorem through_p_adapt {c : Codec} (f g : Value → Value) :
    (c.through f g).p = (c.adapt (some ∘ f) (some ∘ g)).p := by
  funext a; simp only [Codec.through, Codec.adapt]; cases c.p a <;> rfl

/-- `refine` writes as `adapt` with a partial identity — the *same* combinator, weaker
    adapter. This is the sense in which it is sugar. -/
theorem restrict_e_adapt {c : Codec} (q : Value → Bool) :
    (c.restrict q).e = (c.adapt (partialId q) (partialId q)).e := by
  funext v; simp only [Codec.restrict, Codec.adapt, partialId]; cases q v <;> rfl

/-- …and reads as one. -/
theorem restrict_p_adapt {c : Codec} (q : Value → Bool) :
    (c.restrict q).p = (c.adapt (partialId q) (partialId q)).p := by
  funext a; simp only [Codec.restrict, Codec.adapt, partialId]; rfl

/-! ### §1's number gates are that combinator too

    `(number)` and `(decimal)` each carry a predicate checked on **both** halves —
    `Numeral.WF` on the double a text reads back to, `Numeral.Stored` on the numeral a
    string is written as. §3 argues at length that gating only the write breaks (C), which
    is exactly the shape `restrict` has and an ad-hoc `if` does not.

    So the gates are not bespoke: each of the two codecs is `refine` over a base, and the
    theorems below say so on the pair. The bases used to be *ungated* — every double, every
    string — and cannot be, now that `Attr.n` carries §1's `Numerals`. They are §1's own
    sets instead: `numberCodec` on the double side, `wfDecimalCodec` on the text side.
    That is a better presentation than the one it replaced, because the ungated bases were
    standing in for sets the carrier should have been. -/

/-- §1's `D`, as a predicate on values. -/
noncomputable def inD : Value → Bool :=
  fun v => match v with | .num d => Numeral.WF d.toDec | _ => false

/-- §1's `Stored`, likewise. -/
def isStored : Value → Bool :=
  fun v => match v with | .str s => Numeral.Stored s | _ => false

/-- **`number` writes exactly on §1's `D`**, and **`decimal` exactly on `Stored`** —
    stated as the `isSome` of the write, without the `dite`.

    Worth having as lemmas rather than leaving to `simp`: the decision inside those `dite`s
    is `Numeral.WF`, whose body is a string parser (`Domain.lean`), so any `simp` that
    unfolds the codec will chase the parser and run out of heartbeats. These state the only
    consequence the analysis rows need.

    `restrict_e_isSome` is the same move one level up: a refinement writes where the gate
    passes and the base writes, so a row can read off a refinement without unfolding it. -/
@[simp] theorem restrict_e_isSome {c : Codec} {q : Value → Bool} (v : Value) :
    ((c.restrict q).e v).isSome = (q v && (c.e v).isSome) := by
  simp only [Codec.restrict]
  by_cases h : q v = true <;> simp [h]

@[simp] theorem numberCodec_e_isSome (v : Value) : (numberCodec.e v).isSome = inD v := by
  cases v <;> try rfl
  case num d =>
    rw [numberCodec_e_num]; by_cases h : Numeral.WF d.toDec = true <;> simp [inD, h]

@[simp] theorem decimalCodec_e_isSome (v : Value) :
    (decimalCodec.e v).isSome = isStored v := by
  cases v <;> try rfl
  case str s =>
    show (if h : Numeral.Stored s then some (Attr.n ⟨s, Numeral.stored_wf h⟩) else none).isSome
      = isStored (Value.str s)
    by_cases h : Numeral.Stored s = true <;> simp [isStored, h]

/-! ### The base at `N` is §1's own set, not an ungated one

**There is no ungated numeric base**, because `Attr.n` carries `Numeral.WF`: an ungated
numeric codec would have to write an attribute `𝔸` has no point for. So `numberCodec` **is**
the base on the double side — §1's `Numerals` is the whole of `Carries(N)`, and there is no
wider codec to refine — and `wfDecimalCodec` is the base on the text side, gated at `WF`,
which is the largest decimal codec the carrier permits. The refinements below refine §1's own
sets. -/

/-- `decimal` before its *storage* gate: every numeral §1 accepts, held as its own text.
    Gated at `WF` and not at `Stored`, which is exactly the difference `decimal` adds. -/
def wfDecimalCodec : Codec :=
  { T := fun v => ∃ s, v = .str s ∧ Numeral.WF s = true
    μ := some .N
    e := fun v => match v with
      | .str s => if h : Numeral.WF s then some (.n ⟨s, h⟩) else none
      | _ => none
    p := fun a => match a with | .n x => some (.str x.1) | _ => none }

/-- **§3's `(decimal)` gate is `refine`** at `Stored` over §1's `Numerals`, on the writing
    half… The base is `wfDecimalCodec` rather than an ungated one, and `Stored → WF` is
    what makes the composite equal `decimal`. -/
theorem decimalCodec_e_restrict : decimalCodec.e = (wfDecimalCodec.restrict isStored).e := by
  funext v; cases v with
  | str s =>
    by_cases hs : Numeral.Stored s = true
    · have hw := Numeral.stored_wf hs
      simp [decimalCodec, wfDecimalCodec, Codec.restrict, isStored, hs, hw]
    · simp [decimalCodec, wfDecimalCodec, Codec.restrict, isStored, hs]
  | _ => rfl

/-- …and on the reading half. -/
theorem decimalCodec_p_restrict : decimalCodec.p = (wfDecimalCodec.restrict isStored).p := by
  funext a; cases a with
  | n x =>
    by_cases hs : Numeral.Stored x.1 = true <;>
      simp [decimalCodec, wfDecimalCodec, Codec.restrict, isStored, hs]
  | _ => rfl

/-- §3 `(literal)`. **The pair is a refinement of its base by construction** — the `refine`
    §7 calls "an iso and a prism", with the prism named by `ℓ` and the iso supplied by the
    index.

    **`T` is deliberately *not* the refinement's**: it stays §3's `ℓ`. That used to mean a
    numeric literal outside `D` was *held* and unwritable — (B) failing — and it no longer can
    be, because `GroundKind.number`'s carrier is `WFDouble`, so `HLit` holds only values
    `numberCodec` writes. What (B) failing looks like is stated on `literalNRule`
    (`Refutations.lean`), a prism over an ungated `ℓ` that is not a `Term`. -/
noncomputable def literalCodec (k : GroundKind) (ls : NEFinset k.Carrier) : Codec :=
  { (baseCodec k).restrict (inL k ls) with T := HLit k ls }

theorem literalNCodec_p_n (ls : NEFinset WFDouble) (x : WFNumeral) :
    (literalCodec .number ls).p (.n x) =
      (numberCodec.p (.n x)).bind (fun v => if inL .number ls v then some v else none) := rfl

/-! ### The gated ground codecs are refinements

`literal` is not a new construction: it is `string` and `number` with a prism laid over
them, which is exactly what §7 means by "an iso and a prism". Naming the predicates makes
that visible, and lets all four of its laws come from `Lawful.restrict` and
`carrier_restrict` instead of four bespoke inductions.

`decimal` is deliberately *not* here. It moves the member (`str` values to an `N`
attribute), so it is not a refinement of `string` and keeps its own proofs. -/

/-- **§3's gate is `refine` over the base, at every base** — and the numeric one is `number`
    itself rather than an ungated stand-in, because §1's `Numerals` is the whole of
    `Carries(N)` and there is no wider numeric pair. That is what makes numeric literals
    separable: see `uniqueAdmission_of_sharedBase`.

    Both halves are `rfl` now, where the string pair needed a `funext` and a case split: the
    codec *is* the restriction, rather than a hand-written pair that agreed with one. -/
theorem literalCodec_e_restrict (k : GroundKind) (ls : NEFinset k.Carrier) :
    (literalCodec k ls).e = ((baseCodec k).restrict (inL k ls)).e := rfl

theorem literalCodec_p_restrict (k : GroundKind) (ls : NEFinset k.Carrier) :
    (literalCodec k ls).p = ((baseCodec k).restrict (inL k ls)).p := rfl

/-- The member is the base's, and the base's is the index's. -/
theorem literalCodec_μ (k : GroundKind) (ls : NEFinset k.Carrier) :
    (literalCodec k ls).μ = some k.member := by cases k <;> rfl

/-- Membership in `ℓ` places the value in the held set — the direction `Carrier` needs, and
    the one place `.null`'s nonemptiness is used for anything. -/
theorem hLit_of_inL (k : GroundKind) (ls : NEFinset k.Carrier) (v : Value) :
    inL k ls v = true → HLit k ls v := by
  cases k <;> cases v <;> intro h <;>
    first
      | exact Bool.noConfusion h
      | exact ⟨_, by simpa [inL] using h, rfl⟩
      -- **The two gated bases reach here and the four ungated ones do not.** Their rows are a
      -- `dite` on the gate, so the alternative above — which expects the value's payload to
      -- *be* the carrier — cannot see through it. Splitting on the gate names the alternative
      -- as a subtype, and `toValue` projects it straight back. `cases hs :` rather than
      -- `by_cases`, which is classical. `number` joined `decimal` here when `ℓ ⊆ D` moved from
      -- ~~LiteralD~~ into `WFDouble`; the two branches differ only in which gate they split.
      | exact (by
          rename_i s
          cases hs : Numeral.Stored s with
          | false => simp [inL, hs] at h
          | true => exact ⟨⟨s, hs⟩, by simpa [inL, hs] using h, rfl⟩)
      | exact (by
          rename_i d
          cases hs : Numeral.WF d.toDec with
          | false => simp [inL, hs] at h
          | true => exact ⟨⟨d, hs⟩, by simpa [inL, hs] using h, rfl⟩)
      -- `.null`'s carrier is `Unit`, so the alternative is whichever one the nonemptiness
      -- proof names. Destructed rather than `choose`n: `Exists.choose` is `Classical.choice`,
      -- and `formal/` advertises its absence.
      | exact (by obtain ⟨x, hx⟩ := ls.2; exact ⟨x, hx, rfl⟩)

/-- `legacy`: extend the reading. With §3's coherence premise this presentation equals
    the order-free `p ∪ r`. -/
def Codec.extendRead (c : Codec) (r : Attr → Option Value) : Codec :=
  { T := c.T
    μ := c.μ
    e := c.e
    p := fun a => match c.p a with | some v => some v | none => r a }

/-- **Adjoining a point**, on either side. `nullable` does this twice — the null value to
    the writing half, the `⟨NULL, ∗⟩` attribute to the reading half — and the two are the
    same construction at two carriers. Stating it once is what makes `orNull_e` and
    `orNull_p` one theorem rather than a theorem and its mirror. -/
def addPoint {A B : Type} (isPt : A → Bool) (pt : B) (f : A → Option B) : A → Option B :=
  fun x => if isPt x then some pt else f x

/-- `nullable`. -/
def Codec.orNull (c : Codec) : Codec :=
  { T := fun v => c.T v ∨ v = .null
    μ := none
    e := addPoint (· matches .null) .null c.e
    p := addPoint (· matches .null) .null c.p }

/-! ### What the wrappers write and read

Each wrapper is one line of definition and touches exactly one half of the pair; stating
that as an `iff` is what keeps the proofs below — and §6's wrapper rows — from unfolding
the definitions again. `held` and `legacy` are transparent on the side they do not
touch, which is why two of the eight are `Iff.rfl`. -/

section WrapperInversion
variable {c : Codec}

/-- `held` writes what its base writes, at the transported value. -/
theorem through_e {f g : Value → Value} {v a} :
    (c.through f g).e v = some a ↔ c.e (f v) = some a := Iff.rfl

/-- …and reads what its base reads, transported back. -/
theorem through_p {f g : Value → Value} {a v} :
    (c.through f g).p a = some v ↔ ∃ w, c.p a = some w ∧ v = g w := by
  simp [Codec.through, Option.map_eq_some_iff, eq_comm (a := v)]

/-- The read side of `restrict_e_isSome`, and its absence is why every literal row unfolded
    `Codec.restrict` by hand. §4c asks for one codec stated once for both sides; the write half
    was `@[simp]` and the read half was not there. -/
@[simp] theorem restrict_p_isSome {c : Codec} {q : Value → Bool} (a : Attr) :
    ((c.restrict q).p a).isSome = ((c.p a).elim false q) := by
  simp only [Codec.restrict]
  cases c.p a with
  | none => rfl
  | some v => cases hq : q v <;> simp [hq]

/-- `refine` writes only what passes the prism… -/
theorem restrict_e {q : Value → Bool} {v a} :
    (c.restrict q).e v = some a ↔ q v = true ∧ c.e v = some a := by
  simp only [Codec.restrict]; split <;> simp_all

/-- …and reads only into it. -/
theorem restrict_p {q : Value → Bool} {a v} :
    (c.restrict q).p a = some v ↔ c.p a = some v ∧ q v = true := by
  simp only [Codec.restrict, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨w, hw, h⟩; split at h <;> simp_all
  · rintro ⟨h, hq⟩; exact ⟨v, h, by simp [hq]⟩

/-- `legacy` does not touch the writing at all — §5's whole point. -/
theorem extendRead_e {r : Attr → Option Value} {v a} :
    (c.extendRead r).e v = some a ↔ c.e v = some a := Iff.rfl

/-- It reads through the base where the base reads, and through the migration exactly
    where the base does not. That "exactly" is where (MP) goes. -/
theorem extendRead_p {r : Attr → Option Value} {a v} :
    (c.extendRead r).p a = some v ↔ c.p a = some v ∨ (c.p a = none ∧ r a = some v) := by
  show (match c.p a with | some w => some w | none => r a) = some v ↔ _
  cases hp : c.p a <;> simp

/-- `nullable` adds the `null` point and passes everything else through — `addPoint` at
    the value carrier. -/
theorem orNull_e {v a} :
    c.orNull.e v = some a ↔ (v = .null ∧ a = .null) ∨ (v ≠ .null ∧ c.e v = some a) := by
  cases v <;> simp [Codec.orNull, addPoint, eq_comm (a := a)]

/-- …and the same construction at the attribute carrier. -/
theorem orNull_p {a v} :
    c.orNull.p a = some v ↔ (a = .null ∧ v = .null) ∨ (a ≠ .null ∧ c.p a = some v) := by
  cases a <;> simp [Codec.orNull, addPoint, eq_comm (a := v)]

end WrapperInversion


/-- Lawfulness sees only the pair and the member, so it transfers to any codec agreeing on
    those three. This is how a ground codec inherits from the wrapper it turns out to be,
    without disturbing its definition — which matters, since the definitions are unfolded
    all over the development. -/
theorem Lawful.congr {c d : Codec} (he : c.e = d.e) (hp : c.p = d.p) (hμ : c.μ = d.μ)
    (h : Lawful d) : Lawful c := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t a hx; rw [he] at hx; rw [hp]; exact h.retract hx
  · intro a t hx; rw [hp] at hx; rw [he]; exact h.canon hx
  · intro μ hm t a hx; rw [hμ] at hm; rw [he] at hx; exact h.writes hm hx
  · intro a t a' h1 h2; rw [hp] at h1; rw [he] at h2; exact h.agree h1 h2

/-- The carrier transfers too, given the held set is no smaller. -/
theorem Carrier.congr {c d : Codec} (he : c.e = d.e) (hp : c.p = d.p)
    (hT : ∀ v, d.T v → c.T v) (h : Carrier d) : Carrier c := by
  refine ⟨?_, ?_⟩
  · intro v a hx; rw [he] at hx; exact hT v (h.domE hx)
  · intro a v hx; rw [hp] at hx; exact hT v (h.ranP hx)

/-- Forgetting the member index preserves the laws — `(lazy)` concludes `⊤`. -/
theorem Lawful.μNone {c : Codec} (h : Lawful c) : Lawful { c with μ := none } := by
  refine ⟨h.retract, h.canon, ?_, h.agree⟩
  intro _ h'
  exact nomatch h'

theorem LawfulCore.μNone {c : Codec} (h : LawfulCore c) :
    LawfulCore { c with μ := none } := by
  refine ⟨h.retract, h.canon, ?_⟩
  intro _ h'
  exact nomatch h'

end

end Calculus
