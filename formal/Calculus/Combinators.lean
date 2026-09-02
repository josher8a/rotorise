import Calculus.Lists
import Calculus.Codec

/-!
# Certified combinators

The semantic constructions the denotation factors through, each carrying its own
lawfulness lemma — so soundness becomes plumbing rather than eighteen bespoke cases.
The inventory mirrors the doc's own analysis (§7: products and coproducts are the
irreducible structure; everything else wraps one subterm):

* ground codecs — one per §3 ground term — **proved**;
* `through` / `restrict` — the iso/prism pair (`held`, `refine`), the
  invertible-syntax-descriptions combinator the doc cites — **proved**;
* `extendRead` — the agreeing extension of the reading (`legacy`) — core laws
  **proved**; (MP) is the sanctioned breach and has no lemma, by design;
* `orNull` — `nullable`, whose honesty premises are (U) for a two-option sum,
  specialised — **proved**;
* the **traversal toolkit** (`traverse` and the round-trip / definedness /
  pointwise-relation lemmas — **proved**): the one proof shape shared by every
  product. `drop` is a *filter*, not a traversal mode, and `tuple` is `align` +
  `traverse` — so nothing needs a second toolkit;
* products — `carriedCodec`, a payload pair carried between two prisms, is the shape
  underneath all of them; `entrywise` is it at a traversal (hence `arrayCodec` and
  `recordCodec`), `tupleCodec` it at `align` + a traversal, where the one fact worth
  proving is that alignment depends on a row's *length* alone (`slots`, `align_eq_some`).
  `setCodec` and `objectCodec` are argued on their own;
* sums — `altCodec` over `OptionSem`s that carry their *admission as data*, with
  `UniqueAdmission` ((U) as a premise). `dunionCodec` is `altCodec` over
  tag-admission options — "the one union whose (U) is a theorem" (doc §5) is
  literally `uniqueAdmission_byTag`. `opaqCodec` is `altCodec`'s fueled fixpoint
  over everything self-identifying — its (U) is `uniqueAdmission_opaque`, and
  the `refuse` policy is the absence of the number option.
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

/-- A map's payload: the name set, and the values on it. A dependent pair rather than a
    list of pairs, because that is what `M` is — see `Attr.m`. -/
abbrev MapOf (α : Type) := Σ keys : Finset Name, {k // k ∈ keys} → α

/-- Two map payloads are equal when their name sets are and their values agree on them.
    The dependent pair needs this said once; the list representation got it from
    `List.ext`. -/
theorem MapOf.ext {α : Type} {p q : MapOf α} (hk : p.1 = q.1)
    (hf : ∀ k (h₁ : k ∈ p.1) (h₂ : k ∈ q.1), p.2 ⟨k, h₁⟩ = q.2 ⟨k, h₂⟩) : p = q := by
  obtain ⟨kp, fp⟩ := p
  obtain ⟨kq, fq⟩ := q
  cases hk
  exact congrArg (Sigma.mk kp) (funext fun k => hf k.1 k.2 k.2)

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
`fanOf` found behind `AdmA_exact`'s duplication. `number` and `decimal` get no equation here:
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
  funext a; simp only [Codec.restrict, Codec.adapt, partialId]

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
  simp [Codec.through, Option.map_eq_some', eq_comm (a := v)]

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
  simp only [Codec.restrict, Option.bind_eq_some]
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

/-! ## Filter facts (the sum proofs consume these) -/


/-! ## Products -/

/-- **The set image.** Map a finite set through a partial function, refusing if an element
    fails *or if two elements collide*.

    Not `Finset.image`, for two reasons. It dedups, which is the wrong answer here — (R)
    needs the element map injective, and collapsing two elements makes `p (e v) = v`
    unsatisfiable — so a collision must be refused, not absorbed. And its API is classical:
    `Finset.mem_image` and `Multiset.mem_dedup` depend on `Classical.choice`, which §3's
    axiom base does not admit. A `Nodup`-guarded `Multiset.map` needs neither. -/
noncomputable def setImage {α β : Type} [DecidableEq β]
    (f : α → Option β) (S : Finset α) : Option (Finset β) :=
  if h : ∀ x ∈ S, (f x).isSome then
    if hn : (S.attach.val.map (fun x => (f x.1).get (h x.1 x.2))).Nodup then
      some ⟨_, hn⟩
    else none
  else none

/-- Every element of the source maps. -/
theorem setImage_some {α β : Type} [DecidableEq β] {f : α → Option β} {S : Finset α}
    {T : Finset β} (h : setImage f S = some T) : ∀ x ∈ S, (f x).isSome := by
  unfold setImage at h
  split at h
  · next hall => exact hall
  · exact nomatch h

/-- …and the image contains exactly the elements' images. -/
theorem mem_setImage {α β : Type} [DecidableEq β] {f : α → Option β} {S : Finset α}
    {T : Finset β} (h : setImage f S = some T) (y : β) :
    y ∈ T ↔ ∃ x ∈ S, f x = some y := by
  unfold setImage at h
  split at h
  · next hall =>
    split at h
    · next hn =>
      injection h with h
      subst h
      constructor
      · intro hy
        simp only [Finset.mem_mk, Multiset.mem_map] at hy
        obtain ⟨x, -, hxy⟩ := hy
        exact ⟨x.1, x.2, by rw [← hxy]; exact (Option.some_get (hall x.1 x.2)).symm⟩
      · rintro ⟨x, hx, hfx⟩
        simp only [Finset.mem_mk, Multiset.mem_map]
        refine ⟨⟨x, hx⟩, Multiset.mem_attach _ _, ?_⟩
        rw [Option.get_of_mem (hall x hx) hfx]
    · exact nomatch h
  · exact nomatch h

/-- A non-empty set has a non-empty image. -/
theorem setImage_nonempty {α β : Type} [DecidableEq β] {f : α → Option β} {S : Finset α}
    {T : Finset β} (h : setImage f S = some T) (hs : S.Nonempty) : T.Nonempty := by
  obtain ⟨x, hx⟩ := hs
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (setImage_some h x hx)
  exact ⟨y, (mem_setImage h y).mpr ⟨x, hx, hy⟩⟩

/-- **The set image at `℘⁺fin`.** The same map, with non-emptiness carried rather than
    re-derived: `setImage_nonempty` is spent once, here, instead of at every call site.
    Everything else known about `setImage` transports through `neSetImage_eq_setImage`. -/
noncomputable def neSetImage {α β : Type} [DecidableEq β]
    (f : α → Option β) (S : NEFinset α) : Option (NEFinset β) :=
  match h : setImage f S.1 with
  | some T => some ⟨T, setImage_nonempty h S.2⟩
  | none => none

theorem neSetImage_eq_setImage {α β : Type} [DecidableEq β] {f : α → Option β}
    {S : NEFinset α} {T : NEFinset β} :
    neSetImage f S = some T ↔ setImage f S.1 = some T.1 := by
  unfold neSetImage
  split
  · next T' hT' =>
      refine ⟨fun h => ?_, fun h => ?_⟩
      · cases h; exact hT'
      · rw [hT'] at h; injection h with h; exact congrArg some (Subtype.ext h)
  · next hT' =>
      exact Iff.intro (fun h => nomatch h) (fun h => by rw [hT'] at h; exact nomatch h)

/-- …and `none` transports too. -/
theorem neSetImage_none {α β : Type} [DecidableEq β] {f : α → Option β} {S : NEFinset α}
    (h : setImage f S.1 = none) : neSetImage f S = none := by
  unfold neSetImage; split
  · next T' hT' => rw [h] at hT'; exact nomatch hT'
  · rfl

/-- **The constructor for `setImage`.** Given that every element maps, that the map is
    injective on the set, and a candidate image with the right membership, the image *is*
    that candidate. The injectivity hypothesis is what (R) supplies, and what `Finset.image`
    would have thrown away by dedupping. -/
theorem setImage_eq {α β : Type} [DecidableEq β] {f : α → Option β} {S : Finset α}
    {U : Finset β}
    (hall : ∀ x ∈ S, (f x).isSome)
    (hinj : ∀ x₁ ∈ S, ∀ x₂ ∈ S, ∀ y, f x₁ = some y → f x₂ = some y → x₁ = x₂)
    (hmem : ∀ y, y ∈ U ↔ ∃ x ∈ S, f x = some y) :
    setImage f S = some U := by
  unfold setImage
  rw [dif_pos hall]
  have hnd : (S.attach.val.map (fun x => (f x.1).get (hall x.1 x.2))).Nodup := by
    refine Multiset.Nodup.map_on ?_ S.attach.nodup
    intro x hx y hy hxy
    have hfx : f x.1 = some ((f x.1).get (hall x.1 x.2)) := (Option.some_get _).symm
    have hfy : f y.1 = some ((f y.1).get (hall y.1 y.2)) := (Option.some_get _).symm
    rw [hxy] at hfx
    exact Subtype.ext (hinj x.1 x.2 y.1 y.2 _ hfx hfy)
  rw [dif_pos hnd]
  congr 1
  apply Finset.ext
  intro y
  simp only [Finset.mem_mk, Multiset.mem_map, hmem y]
  constructor
  · rintro ⟨x, -, hxy⟩
    exact ⟨x.1, x.2, by rw [← hxy]; exact (Option.some_get (hall x.1 x.2)).symm⟩
  · rintro ⟨x, hx, hfx⟩
    exact ⟨⟨x, hx⟩, Multiset.mem_attach _ _, by rw [Option.get_of_mem (hall x hx) hfx]⟩

/-- **Inversion.** If the element map has a left inverse on its image, the set image
    inverts too. This is (R) lifted from elements to sets, and it is where the collision
    guard earns its place: without injectivity the image would be smaller than the source
    and could not invert. -/
theorem setImage_inv {α β : Type} [DecidableEq α] [DecidableEq β]
    {f : α → Option β} {g : β → Option α} {S : Finset α} {T : Finset β}
    (hfg : ∀ x y, f x = some y → g y = some x)
    (h : setImage f S = some T) : setImage g T = some S := by
  refine setImage_eq ?_ ?_ ?_
  · intro y hy
    obtain ⟨x, hx, hfx⟩ := (mem_setImage h y).mp hy
    rw [hfg x y hfx]; rfl
  · intro y₁ hy₁ y₂ hy₂ x hg₁ hg₂
    obtain ⟨x₁, hx₁, hf₁⟩ := (mem_setImage h y₁).mp hy₁
    obtain ⟨x₂, hx₂, hf₂⟩ := (mem_setImage h y₂).mp hy₂
    rw [hfg x₁ y₁ hf₁] at hg₁
    rw [hfg x₂ y₂ hf₂] at hg₂
    cases Option.some.inj hg₁
    cases Option.some.inj hg₂
    exact Option.some.inj (hf₁.symm.trans hf₂)
  · intro x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (setImage_some h x hx)
      exact ⟨y, (mem_setImage h y).mpr ⟨x, hx, hy⟩, hfg x y hy⟩
    · rintro ⟨y, hy, hgy⟩
      obtain ⟨x', hx', hf'⟩ := (mem_setImage h y).mp hy
      rw [hfg x' y hf'] at hgy
      cases Option.some.inj hgy
      exact hx'

/-- The round trip a set needs, assembled from the element codec's. -/
theorem setImage_roundTrip {α β : Type} [DecidableEq α] [DecidableEq β]
    {c : Codec} (h : LawfulCore c) {vinj : α → Value} {aout : Attr → Option β}
    {ainj : β → Attr} {vout : Value → Option α}
    (hA : ∀ a b, aout a = some b → a = ainj b)
    (hV : ∀ x, vout (vinj x) = some x)
    {S : Finset α} {T : Finset β}
    (hI : setImage (fun x => (c.e (vinj x)).bind aout) S = some T) :
    setImage (fun y => (c.p (ainj y)).bind vout) T = some S := by
  refine setImage_inv (fun x y hxy => ?_) hI
  simp only [Option.bind_eq_some] at hxy
  obtain ⟨a, hea, hoa⟩ := hxy
  rw [hA a y hoa] at hea
  rw [h.retract hea]
  simpa using hV x

/-- One failing element sinks the image. -/
theorem setImage_none_of {α β : Type} [DecidableEq β] {f : α → Option β} {S : Finset α}
    {x : α} (hx : x ∈ S) (hf : f x = none) : setImage f S = none := by
  unfold setImage
  rw [dif_neg]
  intro hall
  have := hall x hx
  rw [hf] at this
  exact absurd this (by simp)

/-- The image succeeds when every element maps and no two collide. -/
theorem setImage_isSome_of {α β : Type} [DecidableEq β] {f : α → Option β} {S : Finset α}
    (hall : ∀ x ∈ S, (f x).isSome)
    (hinj : ∀ x₁ ∈ S, ∀ x₂ ∈ S, ∀ y, f x₁ = some y → f x₂ = some y → x₁ = x₂) :
    (setImage f S).isSome = true := by
  unfold setImage
  rw [dif_pos hall]
  have hnd : (S.attach.val.map (fun x => (f x.1).get (hall x.1 x.2))).Nodup := by
    refine Multiset.Nodup.map_on ?_ S.attach.nodup
    intro x hx y hy hxy
    have hfx : f x.1 = some ((f x.1).get (hall x.1 x.2)) := (Option.some_get _).symm
    have hfy : f y.1 = some ((f y.1).get (hall y.1 y.2)) := (Option.some_get _).symm
    rw [hxy] at hfx
    exact Subtype.ext (hinj x.1 x.2 y.1 y.2 _ hfx hfy)
  rw [dif_pos hnd]
  rfl

/-- **The image only looks at the set.** Two element maps agreeing on `S` have the same
    image — needed because `Codec.restrict` changes `e` everywhere and the set only sees it
    at its own members. -/
theorem setImage_congr {α β : Type} [DecidableEq β] {f g : α → Option β} {S : Finset α}
    (h : ∀ x ∈ S, f x = g x) : setImage f S = setImage g S := by
  have hiff : (∀ x ∈ S, (f x).isSome) ↔ (∀ x ∈ S, (g x).isSome) :=
    ⟨fun hh x hx => (h x hx) ▸ hh x hx, fun hh x hx => (h x hx).symm ▸ hh x hx⟩
  unfold setImage
  split
  · next hf =>
    have hg := hiff.mp hf
    rw [dif_pos hg]
    have hmap : (S.attach.val.map (fun x => (f x.1).get (hf x.1 x.2)))
        = (S.attach.val.map (fun x => (g x.1).get (hg x.1 x.2))) := by
      refine Multiset.map_congr rfl (fun x _ => ?_)
      exact Option.some.inj (by rw [Option.some_get, Option.some_get, h x.1 x.2])
    simp only [hmap]
  · next hf =>
    rw [dif_neg (fun hg => hf (hiff.mpr hg))]

/-- …and the same at `℘⁺fin`. -/
theorem neSetImage_congr {α β : Type} [DecidableEq β] {f g : α → Option β} {S : NEFinset α}
    (h : ∀ x ∈ S.1, f x = g x) : neSetImage f S = neSetImage g S := by
  cases hs : setImage f S.1 with
  | none => rw [neSetImage_none hs, neSetImage_none ((setImage_congr h).symm.trans hs)]
  | some T =>
    have hT : setImage g S.1 = some T := (setImage_congr h).symm.trans hs
    rw [(neSetImage_eq_setImage (T := ⟨T, setImage_nonempty hs S.2⟩)).mpr hs,
      (neSetImage_eq_setImage (T := ⟨T, setImage_nonempty hs S.2⟩)).mpr hT]

/-- A successful `bind` needs a successful left. -/
theorem bind_isSome_left {α β : Type} {o : Option α} {f : α → Option β}
    (h : (o.bind f).isSome = true) : o.isSome = true := by
  cases o <;> simp_all

/-- Reading a value's scalar payload, the mirror of `sC`/`nC`/`bC` on the value side. -/
def vStr : Value → Option String := fun v => match v with | .str s => some s | _ => none
def vNum : Value → Option Double := fun v => match v with | .num d => some d | _ => none
def vBin : Value → Option Bytes  := fun v => match v with | .bin b => some b | _ => none

/-- A `bind` through a value projection pins the value. -/
theorem bind_vStr {o : Option Value} {y : String} (h : o.bind vStr = some y) :
    o = some (.str y) := by
  cases o with
  | none => exact nomatch h
  | some w => cases w <;> simp_all [vStr]

theorem bind_vNum {o : Option Value} {y : Double} (h : o.bind vNum = some y) :
    o = some (.num y) := by
  cases o with
  | none => exact nomatch h
  | some w => cases w <;> simp_all [vNum]

theorem bind_vBin {o : Option Value} {y : Bytes} (h : o.bind vBin = some y) :
    o = some (.bin y) := by
  cases o with
  | none => exact nomatch h
  | some w => cases w <;> simp_all [vBin]

/-- The member a set stores, computed from its element's (§3 `(set)`). -/
def setMember : Member → Option Member
  | .S => some .SS
  | .N => some .NS
  | .B => some .BS
  | _ => none

/-- Encode a value-set's payloads into the wire set their member selects. -/
noncomputable def encSet {α : Type} (c : Codec) (inj : α → Value) (S : NEFinset α) :
    Option Attr :=
  match neSetImage (fun x => (c.e (inj x)).bind sC.out) S with
  | some T => some (.ss T)
  | none => match neSetImage (fun x => (c.e (inj x)).bind nC.out) S with
    | some T => some (.ns T)
    | none => (neSetImage (fun x => (c.e (inj x)).bind bC.out) S).map Attr.bs

/-- …and back: decode a wire set's payloads into the value set their kind selects. -/
noncomputable def decSet {α : Type} (c : Codec) (inj : α → Attr) (S : NEFinset α) :
    Option Value :=
  match neSetImage (fun x => (c.p (inj x)).bind vStr) S with
  | some T => some (.strSet T)
  | none => match neSetImage (fun x => (c.p (inj x)).bind vNum) S with
    | some T => some (.numSet T)
    | none => (neSetImage (fun x => (c.p (inj x)).bind vBin) S).map Value.binSet

/-! No emptiness guard here: §1 types the wire sets as `℘⁺fin`, which is a type, so there is
no empty set for a codec to refuse. -/

/-- Writing a set needs every element to write. -/
theorem encSet_elem {α : Type} {c : Codec} {inj : α → Value} {S : NEFinset α} {a : Attr}
    (h : encSet c inj S = some a) : ∀ x ∈ S.1, (c.e (inj x)).isSome = true := by
  unfold encSet at h
  split at h
  · next T hT =>
      exact fun x hx => bind_isSome_left (setImage_some (neSetImage_eq_setImage.mp hT) x hx)
  · split at h
    · next T hT =>
        exact fun x hx => bind_isSome_left (setImage_some (neSetImage_eq_setImage.mp hT) x hx)
    · next =>
      obtain ⟨T, hT, -⟩ := Option.map_eq_some'.mp h
      exact fun x hx => bind_isSome_left (setImage_some (neSetImage_eq_setImage.mp hT) x hx)

/-- …and reading one needs every element to read. -/
theorem decSet_elem {α : Type} {c : Codec} {inj : α → Attr} {S : NEFinset α} {v : Value}
    (h : decSet c inj S = some v) : ∀ x ∈ S.1, (c.p (inj x)).isSome = true := by
  unfold decSet at h
  split at h
  · next T hT =>
      exact fun x hx => bind_isSome_left (setImage_some (neSetImage_eq_setImage.mp hT) x hx)
  · split at h
    · next T hT =>
        exact fun x hx => bind_isSome_left (setImage_some (neSetImage_eq_setImage.mp hT) x hx)
    · next =>
      obtain ⟨T, hT, -⟩ := Option.map_eq_some'.mp h
      exact fun x hx => bind_isSome_left (setImage_some (neSetImage_eq_setImage.mp hT) x hx)

/-- What a read produces: one of the three value sets, each element read from an element
    of the wire set. -/
theorem decSet_mem {α : Type} {c : Codec} {inj : α → Attr} {S : NEFinset α} {v : Value}
    (h : decSet c inj S = some v) :
    (∃ T : NEFinset String, v = .strSet T ∧
        ∀ y ∈ T.1, ∃ x ∈ S.1, c.p (inj x) = some (.str y))
  ∨ (∃ T : NEFinset Double, v = .numSet T ∧
        ∀ y ∈ T.1, ∃ x ∈ S.1, c.p (inj x) = some (.num y))
  ∨ (∃ T : NEFinset Bytes, v = .binSet T ∧
        ∀ y ∈ T.1, ∃ x ∈ S.1, c.p (inj x) = some (.bin y)) := by
  unfold decSet at h
  split at h
  · next T hT =>
    injection h with h
    refine Or.inl ⟨T, h.symm, fun y hy => ?_⟩
    obtain ⟨x, hx, hxy⟩ := (mem_setImage (neSetImage_eq_setImage.mp hT) y).mp hy
    exact ⟨x, hx, bind_vStr hxy⟩
  · split at h
    · next T hT =>
      injection h with h
      refine Or.inr (Or.inl ⟨T, h.symm, fun y hy => ?_⟩)
      obtain ⟨x, hx, hxy⟩ := (mem_setImage (neSetImage_eq_setImage.mp hT) y).mp hy
      exact ⟨x, hx, bind_vNum hxy⟩
    · next =>
      obtain ⟨T, hT, hv⟩ := Option.map_eq_some'.mp h
      refine Or.inr (Or.inr ⟨T, hv.symm, fun y hy => ?_⟩)
      obtain ⟨x, hx, hxy⟩ := (mem_setImage (neSetImage_eq_setImage.mp hT) y).mp hy
      exact ⟨x, hx, bind_vBin hxy⟩

/-- §3 `(set)`. Non-emptiness, uniqueness and homogeneity are all carried by the **types**:
    a `Finset` has no repeats and no order, `℘⁺fin` has no empty inhabitant, and the three
    constructors are the three element types the reference names. What is left for the
    codec is the element map — and that is the whole of `(set)` now. -/
noncomputable def setCodec (c : Codec) : Codec :=
  { T := fun v => match v with
      | .strSet S => ∀ s ∈ S.1, c.T (.str s)
      | .numSet S => ∀ d ∈ S.1, c.T (.num d)
      | .binSet S => ∀ b ∈ S.1, c.T (.bin b)
      | _ => False
    μ := c.μ.bind setMember
    e := fun v => match v with
      | .strSet S => encSet c Value.str S
      | .numSet S => encSet c Value.num S
      | .binSet S => encSet c Value.bin S
      | _ => none
    p := fun a => match a with
      | .ss S => decSet c Attr.s S
      | .ns S => decSet c Attr.n S
      | .bs S => decSet c Attr.b S
      | _ => none }

/-! ### `setCodec` at a base, and the restriction that survives the re-indexing -/

/-- The set's member is the base's, by computation at each of the four. This is §3
    `(set)`'s premise `setMember μ = some μS` discharged once and for all — there is no
    element term left for it to be a premise about. -/
@[simp] theorem SetBase.setCodec_μ : ∀ b : SetBase, (setCodec b.elem).μ = some b.member
  | .string | .number | .decimal | .binary => rfl

/-- The member a base's *elements* store as, as against `SetBase.member`, which is the
    member the **set** stores as. `number` and `decimal` are both `.N` here and both `.NS`
    there. -/
@[simp] def SetBase.elemMember : SetBase → Member
  | .string  => .S
  | .number | .decimal => .N
  | .binary  => .B

@[simp] theorem SetBase.elem_μ : ∀ b : SetBase, b.elem.μ = some b.elemMember
  | .string | .number | .decimal | .binary => rfl

/-- …and `setMember` takes the one to the other, which is the premise `(set)` carried.

    **Not `@[simp]`, and it cannot usefully be.** `SetBase.elemMember` is itself `@[simp]`, so
    `simp` unfolds `b.elemMember` into its `match` before this lemma is ever tried: the
    left-hand side does not exist in simp-normal form, and the attribute could never fire.
    Batteries' `simpNF` linter is what found it (`#lint_calculus`, `Axioms.lean`) — the one
    substantive hit in 1674 declarations. It is named explicitly at its single use site
    (`encSet_isSome_of`, below), which is why the dead attribute cost nothing and hid. -/
theorem SetBase.setMember_elemMember :
    ∀ b : SetBase, setMember b.elemMember = some b.member
  | .string | .number | .decimal | .binary => rfl

/-- **What a set base writes, element by element.** The four ground rows of `Adm`, indexed:
    `string` and `binary` accept their whole carrier, `number` is §1's `D` and `decimal`
    §1's `Stored`. -/
noncomputable def SetBase.adm : SetBase → Value → Bool
  | .string  => fun v => match v with | .str _ => true | _ => false
  | .number  => inD
  | .decimal => isStored
  | .binary  => fun v => match v with | .bin _ => true | _ => false

/-- …and it is exactly the base pair's write domain. -/
theorem SetBase.adm_iff (b : SetBase) (v : Value) :
    b.adm v = true ↔ (b.elem.e v).isSome = true := by
  cases b <;> cases v <;>
    simp [SetBase.adm, SetBase.elem, stringCodec, binaryCodec]

/-- One failing element sinks a write. `encSet_elem` contraposed, in the form the exact
    rows use. -/
theorem encSet_isSome_false {α : Type} {c : Codec} {inj : α → Value} {S : NEFinset α}
    {x : α} (hx : x ∈ S.1) (h : c.e (inj x) = none) : (encSet c inj S).isSome = false := by
  cases he : encSet c inj S with
  | none => rfl
  | some a =>
    have := encSet_elem he x hx
    rw [h] at this; exact absurd this (by simp)

/-- …and a read. -/
theorem decSet_isSome_false {α : Type} {c : Codec} {inj : α → Attr} {S : NEFinset α}
    {x : α} (hx : x ∈ S.1) (h : c.p (inj x) = none) : (decSet c inj S).isSome = false := by
  cases hd : decSet c inj S with
  | none => rfl
  | some v =>
    have := decSet_elem hd x hx
    rw [h] at this; exact absurd this (by simp)

/-- Elements reading to strings take `decSet`'s first branch. The mirror of
    `encSet_isSome_of` at the read side, and it takes injectivity as a hypothesis rather
    than deriving it from `LawfulCore`: the read side's injectivity is **not** free —
    `numberCodec.p` goes through `Double.ofDec`, which rounds. -/
theorem decSet_isSome_str {α : Type} {c : Codec} {inj : α → Attr} {S : NEFinset α}
    (hall : ∀ x ∈ S.1, ((c.p (inj x)).bind vStr).isSome = true)
    (hinj : ∀ x₁ ∈ S.1, ∀ x₂ ∈ S.1, ∀ y, (c.p (inj x₁)).bind vStr = some y →
      (c.p (inj x₂)).bind vStr = some y → x₁ = x₂) :
    (decSet c inj S).isSome = true := by
  obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp (setImage_isSome_of hall hinj)
  unfold decSet
  rw [(neSetImage_eq_setImage (T := ⟨T, setImage_nonempty hT S.2⟩)).mpr hT]
  rfl

/-- …and elements reading to bytes take the third, the two before it having failed. -/
theorem decSet_isSome_bin {α : Type} {c : Codec} {inj : α → Attr} {S : NEFinset α}
    {x₀ : α} (hx₀ : x₀ ∈ S.1)
    (hs : (c.p (inj x₀)).bind vStr = none) (hn : (c.p (inj x₀)).bind vNum = none)
    (hall : ∀ x ∈ S.1, ((c.p (inj x)).bind vBin).isSome = true)
    (hinj : ∀ x₁ ∈ S.1, ∀ x₂ ∈ S.1, ∀ y, (c.p (inj x₁)).bind vBin = some y →
      (c.p (inj x₂)).bind vBin = some y → x₁ = x₂) :
    (decSet c inj S).isSome = true := by
  obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp (setImage_isSome_of hall hinj)
  unfold decSet
  rw [neSetImage_none (setImage_none_of hx₀ hs), neSetImage_none (setImage_none_of hx₀ hn),
    (neSetImage_eq_setImage (T := ⟨T, setImage_nonempty hT S.2⟩)).mpr hT]
  rfl

/-- **A predicate on the elements, lifted to the set.** `q` holding of every member, and
    nothing but a set satisfying it.

    Choice-free, and the reason is worth naming: the test reaches
    `Finset.decidableDforallFinset` and so `Finset.decidableMem`, not
    `DecidableEq (Finset α)` — which is `Classical.choice` and which a subset test written
    as `S ⊆ ls` through `Finset`'s lattice would have pulled in. -/
def liftQ (q : Value → Bool) : Value → Bool
  | .strSet S => decide (∀ s ∈ S.1, q (.str s) = true)
  | .numSet S => decide (∀ d ∈ S.1, q (.num d) = true)
  | .binSet S => decide (∀ b ∈ S.1, q (.bin b) = true)
  | _ => false

/-- A restricted element codec writes a set exactly when every element passes `q` and the
    unrestricted codec writes it. -/
theorem encSet_restrict {α : Type} (c : Codec) (q : Value → Bool) (inj : α → Value)
    (S : NEFinset α) [DecidablePred fun x => q (inj x) = true] :
    encSet (c.restrict q) inj S =
      if decide (∀ x ∈ S.1, q (inj x) = true) then encSet c inj S else none := by
  -- the split is on the **`decide`**, not on the proposition: `by_cases` on the latter
  -- reaches `Classical.em`, which puts `Classical.choice` under everything downstream
  cases hd : decide (∀ x ∈ S.1, q (inj x) = true)
  case true =>
    have hq : ∀ x ∈ S.1, q (inj x) = true := of_decide_eq_true hd
    show encSet (c.restrict q) inj S = encSet c inj S
    unfold encSet
    rw [neSetImage_congr (f := fun x => ((c.restrict q).e (inj x)).bind sC.out)
          (g := fun x => (c.e (inj x)).bind sC.out)
          (fun x hx => by simp only [Codec.restrict, if_pos (hq x hx)]),
        neSetImage_congr (f := fun x => ((c.restrict q).e (inj x)).bind nC.out)
          (g := fun x => (c.e (inj x)).bind nC.out)
          (fun x hx => by simp only [Codec.restrict, if_pos (hq x hx)]),
        neSetImage_congr (f := fun x => ((c.restrict q).e (inj x)).bind bC.out)
          (g := fun x => (c.e (inj x)).bind bC.out)
          (fun x hx => by simp only [Codec.restrict, if_pos (hq x hx)])]
  case false =>
    have hq : ¬ ∀ x ∈ S.1, q (inj x) = true := of_decide_eq_false hd
    show encSet (c.restrict q) inj S = none
    -- the witness is extracted **decidably** too — `by_contra` is the same trap
    obtain ⟨x₀, hx₀, hqx⟩ : ∃ x ∈ S.1, q (inj x) ≠ true :=
      Decidable.byContradiction fun hc =>
        hq fun x hx => Decidable.byContradiction fun h' => hc ⟨x, hx, h'⟩
    cases he : encSet (c.restrict q) inj S with
    | none => rfl
    | some a =>
      have hno := encSet_isSome_false (c := c.restrict q) hx₀
        (show (c.restrict q).e (inj x₀) = none by simp only [Codec.restrict, if_neg hqx])
      rw [he] at hno; exact nomatch hno

/-- **`set(refine(b, q))` is `refine(set(b), liftQ q)` on the write side — on the nose.**

    This is what makes indexing `set` by a base non-lossy. Restricting the *elements* and
    restricting the *set* by the lifted predicate produce the same `e`, so
    `set(literal k ls)` and `set(refine(b, q))` — the two shapes `src/` actually uses
    (`src/codec.set.spec.ts:76`) — are still expressible, as refinements of the set. The
    read side follows from `434e54d`: `restrict`'s `p` decodes and then applies `q`, so
    a set read is admitted exactly when every element it produced passes. -/
theorem setCodec_restrict (c : Codec) (q : Value → Bool) :
    (setCodec (c.restrict q)).e = ((setCodec c).restrict (liftQ q)).e := by
  funext v
  -- each of the three is `encSet_restrict` verbatim: `liftQ q` at a wire family **is** the
  -- `decide` that theorem splits on, same instance, so there is nothing between them
  cases v with
  | strSet S => exact encSet_restrict c q Value.str S
  | numSet S => exact encSet_restrict c q Value.num S
  | binSet S => exact encSet_restrict c q Value.bin S
  | _ => rfl

/-! ### A codec carried between two prisms

The shape underneath every product in §3–§4. A pair works on *payloads* — lists of
entries, mostly — and two prisms say which value and which attribute constructor hold
them. §2's four laws split cleanly along that seam: the prism halves are discharged once,
here, and each construction is left with only its payload pair's own round trip,
definedness and agreement.

`pointCodec` above is the degenerate case, where the payload passes through untouched.
The three below are the products: `entrywise` (a traversal, hence `array` and `record`),
`tuple` (`align`, then a traversal) and `object` (a guard, a filter, then a traversal).

`set` is the one product that is *not* an instance, and for a reason worth stating: its
attribute side is a choice among three wire sets, not one constructor. It is argued on
its own below. -/

/-- **A codec between two prisms.** `P` is the held set's condition on the payload;
    `E`/`D` are the payload pair. -/
def carriedCodec {γ δ : Type} (V : Ctor γ Value) (A : Ctor δ Attr) (μ₀ : Member)
    (P : γ → Prop) (E : γ → Option δ) (D : δ → Option γ) : Codec :=
  { T := fun v => ∃ x, v = V.into x ∧ P x
    μ := some μ₀
    e := fun v => ((V.out v).bind E).map A.into
    p := fun a => ((A.out a).bind D).map V.into }

section Carried
variable {γ δ : Type} {V : Ctor γ Value} {A : Ctor δ Attr} {μ₀ : Member}
  {P : γ → Prop} {E : γ → Option δ} {D : δ → Option γ}

/-- What it writes: only a value the prism matches, and only what `E` accepts. -/
theorem carried_e {v a} :
    (carriedCodec V A μ₀ P E D).e v = some a ↔
      ∃ x y, V.out v = some x ∧ E x = some y ∧ a = A.into y := by
  simp [carriedCodec, Option.bind_eq_some, Option.map_eq_some', eq_comm (a := a)]

/-- What it reads: the mirror. -/
theorem carried_p {a v} :
    (carriedCodec V A μ₀ P E D).p a = some v ↔
      ∃ y x, A.out a = some y ∧ D y = some x ∧ v = V.into x := by
  simp [carriedCodec, Option.bind_eq_some, Option.map_eq_some', eq_comm (a := v)]

/-- (R), (C) and (W) are the payload pair's own, plus the member the attribute
    constructor stamps. The prisms contribute nothing but their two laws. -/
theorem lawfulCore_carried (hμ : ∀ y, (A.into y).member = μ₀)
    (hr : ∀ x y, E x = some y → D y = some x)
    (hc : ∀ y x, D y = some x → (E x).isSome) :
    LawfulCore (carriedCodec V A μ₀ P E D) where
  retract he := by
    obtain ⟨x, y, hv, hx, rfl⟩ := carried_e.mp he
    exact carried_p.mpr ⟨y, x, A.out_into y, hr x y hx, V.into_out hv⟩
  canon hp := by
    obtain ⟨y, x, _, hy, rfl⟩ := carried_p.mp hp
    obtain ⟨y', h'⟩ := Option.isSome_iff_exists.mp (hc y x hy)
    exact Option.isSome_iff_exists.mpr ⟨_, carried_e.mpr ⟨x, y', V.out_into x, h', rfl⟩⟩
  writes := by
    intro μ hμ' t a he
    obtain ⟨_, y, _, _, rfl⟩ := carried_e.mp he
    exact (hμ y).trans (Option.some.inj hμ')

/-- (MP) is the payload pair's own too, stated where it has to be — at the attribute
    constructor, since that is where `≼` is defined. -/
theorem lawful_carried (hμ : ∀ y, (A.into y).member = μ₀)
    (hr : ∀ x y, E x = some y → D y = some x)
    (hc : ∀ y x, D y = some x → (E x).isSome)
    (hag : ∀ y x y', D y = some x → E x = some y' → Agree (A.into y') (A.into y)) :
    Lawful (carriedCodec V A μ₀ P E D) :=
  { lawfulCore_carried hμ hr hc with
    agree := by
      intro a t a' hp he
      obtain ⟨y, x, ha, hy, rfl⟩ := carried_p.mp hp
      obtain ⟨x', y', hv, hx, rfl⟩ := carried_e.mp he
      obtain rfl : x' = x := Option.some.inj ((V.out_into x).symm.trans hv).symm
      exact A.into_out ha ▸ hag _ _ _ hy hx }

/-- `e : T ⇀ 𝔸` and `p : 𝔸 ⇀ T`: the held set's condition has to hold of whatever
    payload either half of the pair accepts. -/
theorem carrier_carried
    (hdom : ∀ {x y}, E x = some y → P x)
    (hran : ∀ {y x}, D y = some x → P x) :
    Carrier (carriedCodec V A μ₀ P E D) where
  domE he := by
    obtain ⟨x, y, hv, hx, _⟩ := carried_e.mp he
    exact ⟨x, V.into_out hv, hdom hx⟩
  ranP hp := by
    obtain ⟨y, x, _, hy, rfl⟩ := carried_p.mp hp
    exact ⟨x, rfl, hran hy⟩

end Carried

/-! ### The entrywise product, named once

`array` and `record` are `carriedCodec` where the payload pair is one entry function
traversed: a value constructor holding a list of entries, an attribute constructor
holding a list of wire entries. Named once, §2's laws are discharged once — and each
instance is left with only the part that is genuinely its own, the shape of `≼` at its
attribute constructor (`Agree.l` compares by position, `Agree.m` by name). -/

/-- **The entrywise product**: `carriedCodec` at a traversal. -/
def entrywise {α β : Type} (V : Ctor (List α) Value) (A : Ctor (List β) Attr)
    (μ₀ : Member) (P : List α → Prop) (f : α → Option β) (g : β → Option α) : Codec :=
  carriedCodec V A μ₀ P (traverse f) (traverse g)

section Entrywise
variable {α β : Type} {V : Ctor (List α) Value} {A : Ctor (List β) Attr}
  {μ₀ : Member} {P : List α → Prop} {f : α → Option β} {g : β → Option α}

/-- The traversal toolkit is exactly what the payload pair's three clauses ask for:
    the round trip reversed, definedness forgotten. -/
theorem lawfulCore_entrywise (hμ : ∀ ys, (A.into ys).member = μ₀)
    (hr : ∀ x y, f x = some y → g y = some x)
    (hc : ∀ y x, g y = some x → (f x).isSome) :
    LawfulCore (entrywise V A μ₀ P f g) :=
  lawfulCore_carried hμ (traverse_roundTrip hr) (traverse_isSome hc)

/-- (MP) is the one clause `array` and `record` do not share: `R` is the entry-level
    agreement the pair delivers, and `hA` is how the attribute constructor turns a
    pointwise `R` into `≼`. -/
theorem lawful_entrywise {R : β → β → Prop} (hμ : ∀ ys, (A.into ys).member = μ₀)
    (hr : ∀ x y, f x = some y → g y = some x)
    (hc : ∀ y x, g y = some x → (f x).isSome)
    (hag : ∀ y x y', g y = some x → f x = some y' → R y' y)
    (hA : ∀ {ys ys' : List β}, ys'.length = ys.length →
            (∀ q ∈ ys'.zip ys, R q.1 q.2) → Agree (A.into ys') (A.into ys)) :
    Lawful (entrywise V A μ₀ P f g) :=
  lawful_carried hμ (traverse_roundTrip hr) (traverse_isSome hc)
    fun _ _ _ hy hx => hA ((traverse_length _ _ hy).trans (traverse_length _ _ hx)).symm
      (traverse_rel hag _ _ _ hy hx)

theorem carrier_entrywise
    (hdom : ∀ {xs ys}, traverse f xs = some ys → P xs)
    (hran : ∀ {ys xs}, traverse g ys = some xs → P xs) :
    Carrier (entrywise V A μ₀ P f g) :=
  carrier_carried hdom hran

end Entrywise

/-! ### `array` (§3) — entrywise between `arr` and `L` -/

/-! ### What `set` writes and reads

    The attribute side of `set` is a choice among three wire constructors rather than
    one prism, which is why it is not an `entrywise` product and why its read-side
    inversion names all three families. -/

/-- What `set` writes: one of the three value-set constructors, its payloads imaged
    through the element codec. -/
theorem setCodec_e_eq {c : Codec} {v : Value} {a : Attr} :
    (setCodec c).e v = some a ↔
      (∃ S : NEFinset String, v = .strSet S ∧ encSet c Value.str S = some a)
      ∨ (∃ S : NEFinset Double, v = .numSet S ∧ encSet c Value.num S = some a)
      ∨ (∃ S : NEFinset Bytes, v = .binSet S ∧ encSet c Value.bin S = some a) := by
  cases v <;> simp [setCodec]

/-- …and what it reads: one of the three wire sets, imaged back. -/
theorem setCodec_p_eq {c : Codec} {a : Attr} {v : Value} :
    (setCodec c).p a = some v ↔
      (∃ S : NEFinset String, a = .ss S ∧ decSet c Attr.s S = some v)
      ∨ (∃ S : NEFinset WFNumeral, a = .ns S ∧ decSet c Attr.n S = some v)
      ∨ (∃ S : NEFinset Bytes, a = .bs S ∧ decSet c Attr.b S = some v) := by
  cases a <;> simp [setCodec]

def arrayCodec (c : Codec) : Codec :=
  { T := fun v => match v with | .arr vs => ∀ x ∈ vs, c.T x | _ => False
    μ := some .L
    e := fun v => match v with
      | .arr vs => (traverse c.e vs).map Attr.l
      | _ => none
    p := fun a => match a with
      | .l as => (traverse c.p as).map Value.arr
      | _ => none }

/-- `array` *is* the entrywise product at `arr`/`L`, on the nose. The definition above is
    left in its unfolded form because the `opaque` fixpoint reduces through it; this
    equation is what carries the three lemmas across. -/
theorem arrayCodec_eq {c : Codec} :
    arrayCodec c = entrywise arrV lA .L (fun vs => ∀ x ∈ vs, c.T x) c.e c.p := by
  ext v <;> cases v <;> simp_all [arrayCodec, entrywise, carriedCodec, arrV, lA, Ctor.into, Ctor.out]

/-- (R), (C), (W) — `L` is the member every `arr` writes. -/
theorem lawfulCore_arrayCodec {c : Codec} (h : LawfulCore c) :
    LawfulCore (arrayCodec c) :=
  arrayCodec_eq ▸ lawfulCore_entrywise (fun _ => rfl) (fun _ _ => h.retract)
    (fun _ _ => h.canon)

/-- `≼` at `L` is positional: `Agree.l` reads the zip the traversal already provides. -/
theorem lawful_arrayCodec {c : Codec} (h : Lawful c) : Lawful (arrayCodec c) :=
  arrayCodec_eq ▸ lawful_entrywise (R := Agree) (fun _ => rfl) (fun _ _ => h.retract)
    (fun _ _ => h.canon) (fun _ _ _ => h.agree) (fun _ hz => .l _ _ hz)

theorem carrier_arrayCodec {c : Codec} (hc : Carrier c) : Carrier (arrayCodec c) :=
  arrayCodec_eq ▸ carrier_entrywise
    (fun h => traverse_mem_input (fun _ _ => hc.domE) h)
    (fun h => traverse_mem (fun _ _ => hc.ranP) h)

/-! ### `record` (§3) — `carriedCodec` between `map` and `M`

The keyed entry steps ~~encPair~~/~~decPair~~ are gone with the traversal. They existed to
carry a name past a codec inside `traverse`, and `M`'s payload no longer has a list for
`traverse` to walk: the names are the index, so `funImage` moves the entry function and
nothing has to carry a name anywhere. Their five laws went with them — §2's four, one
level down, were what `entrywise` asked and `carriedCodec` does not. -/

noncomputable def recordCodec (c : Codec) : Codec :=
  { T := fun v => match v with | .map _ f => ∀ k, c.T (f k) | _ => False
    μ := some .M
    e := fun v => match v with
      | .map keys f => (funImage (fun k => c.e (f k))).map (Attr.m keys)
      | _ => none
    p := fun a => match a with
      | .m keys g => (funImage (fun k => c.p (g k))).map (Value.map keys)
      | _ => none }

/-! `record` is no longer an `entrywise` product: `entrywise` traverses a *list* payload,
and `M`'s payload is a name set with a function on it. What it still is, is `carriedCodec`
between the same two prisms — `carriedCodec` is generic in the payload — so the shape of
the derivation survives even though the traversal does not. These three are direct, and
short, because `funImage` does the work `traverse` used to. -/

/-- What `record` writes and reads: the same name set, every value through `c`. -/
theorem recordCodec_e_eq {c : Codec} {v : Value} {a : Attr} :
    (recordCodec c).e v = some a ↔
      ∃ keys f g, v = .map keys f ∧ funImage (fun k => c.e (f k)) = some g ∧
        a = .m keys g := by
  cases v
  case map keys f =>
    constructor
    · intro h
      obtain ⟨g, hg, rfl⟩ := Option.map_eq_some'.mp h
      exact ⟨keys, f, g, rfl, hg, rfl⟩
    · rintro ⟨keys', f', g, hv, hg, rfl⟩
      cases hv
      show (funImage (fun k => c.e (f k))).map (Attr.m keys) = _
      rw [hg]; rfl
  all_goals
    constructor
    · intro h
      exact nomatch h
    · rintro ⟨_, _, _, hv, -, -⟩
      exact nomatch hv

theorem recordCodec_p_eq {c : Codec} {a : Attr} {v : Value} :
    (recordCodec c).p a = some v ↔
      ∃ keys g f, a = .m keys g ∧ funImage (fun k => c.p (g k)) = some f ∧
        v = .map keys f := by
  cases a
  case m keys g =>
    constructor
    · intro h
      obtain ⟨f, hf, rfl⟩ := Option.map_eq_some'.mp h
      exact ⟨keys, g, f, rfl, hf, rfl⟩
    · rintro ⟨keys', g', f, ha, hf, rfl⟩
      cases ha
      show (funImage (fun k => c.p (g k))).map (Value.map keys) = _
      rw [hf]; rfl
  all_goals
    constructor
    · intro h
      exact nomatch h
    · rintro ⟨_, _, _, ha, -, -⟩
      exact nomatch ha

/-- (R), (C), (W) — `M` is the member every `map` writes. -/
theorem lawfulCore_recordCodec {c : Codec} (h : LawfulCore c) :
    LawfulCore (recordCodec c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t a he
    obtain ⟨keys, f, g, rfl, hg, rfl⟩ := recordCodec_e_eq.mp he
    exact recordCodec_p_eq.mpr ⟨keys, g, f, rfl,
      funImage_eq (fun k => h.retract (funImage_some hg k)), rfl⟩
  · intro a t hp
    obtain ⟨keys, g, f, rfl, hf, rfl⟩ := recordCodec_p_eq.mp hp
    have := funImage_isSome (keys := keys) (g := fun k => c.e (f k))
      (fun k => h.canon (funImage_some hf k))
    simpa [recordCodec] using this
  · intro μ hμ t a he
    obtain ⟨keys, f, g, rfl, -, rfl⟩ := recordCodec_e_eq.mp he
    simpa [Attr.member] using Option.some.inj hμ

/-- `≼` at `M` is by name, and now that is what the constructor says. -/
theorem lawful_recordCodec {c : Codec} (h : Lawful c) : Lawful (recordCodec c) := by
  refine ⟨(lawfulCore_recordCodec h.core).retract, (lawfulCore_recordCodec h.core).canon,
    (lawfulCore_recordCodec h.core).writes, ?_⟩
  intro a t a' hp he
  obtain ⟨keys, g, f, rfl, hf, rfl⟩ := recordCodec_p_eq.mp hp
  obtain ⟨keys', f', g', hv, hg, rfl⟩ := recordCodec_e_eq.mp he
  cases hv
  exact Agree.m keys keys g' g (fun k hx hy =>
    h.agree (funImage_some hf ⟨k, hy⟩) (funImage_some hg ⟨k, hx⟩))

theorem carrier_recordCodec {c : Codec} (hc : Carrier c) : Carrier (recordCodec c) where
  domE {v a} he := by
    obtain ⟨keys, f, g, rfl, hg, rfl⟩ := recordCodec_e_eq.mp he
    exact fun k => hc.domE (funImage_some hg k)
  ranP {a v} hp := by
    obtain ⟨keys, g, f, rfl, hf, rfl⟩ := recordCodec_p_eq.mp hp
    exact fun k => hc.ranP (funImage_some hf k)

/-! ### `tuple` (§3) — the positional product

`tuple` is `carriedCodec` between the same two prisms as `array`, with a payload pair
that pairs each position with its own codec before traversing. Everything specific to it
is therefore a fact about that pairing, and there is only one worth stating: **which
codec a position gets depends on the position alone, never on what stands there.** Name
the codec row a shape assigns to a row of `n` positions (`slots`) and the pairing is a
`zip` with it (`align_eq_some`) — after which a row and its image under the pair, having
the same length, provably align against the *same* codecs. That is the whole of the
tuple's asymmetry between reading and writing, and the four clauses of §2 then run
position by position over the codec row, exactly as they do for `array`. -/

/-- Pair each position with its codec: the fixed head positionally, the tail
    uniformly; length mismatches refuse. `tuple` is then `align` + `traverse`. -/
def align {α : Type} : List Codec → Option Codec → List α → Option (List (Codec × α))
  | [], _, [] => some []
  | [], tail, x :: xs =>
    match tail with
    | some c => (align [] tail xs).map ((c, x) :: ·)
    | none => none
  | _ :: _, _, [] => none
  | c :: cs, tail, x :: xs => (align cs tail xs).map ((c, x) :: ·)

def tupleCodec (cs : List Codec) (tail : Option Codec) : Codec :=
  { T := fun v => match v with
      | .arr vs => ∃ ps, align cs tail vs = some ps ∧ ∀ p ∈ ps, p.1.T p.2
      | _ => False
    μ := some .L
    e := fun v => match v with
      | .arr vs => ((align cs tail vs).bind
          (traverse fun cv => cv.1.e cv.2)).map Attr.l
      | _ => none
    p := fun a => match a with
      | .l as => ((align cs tail as).bind
          (traverse fun ca => ca.1.p ca.2)).map Value.arr
      | _ => none }

/-! #### The codec row a shape assigns -/

/-- The codec row for a row of `n` positions: the fixed head, then the tail codec as
    often as needed. `none` is the length mismatch `align` refuses on. -/
def slots : List Codec → Option Codec → Nat → Option (List Codec)
  | [], _, 0 => some []
  | [], none, _ + 1 => none
  | [], some c, n + 1 => (slots [] (some c) n).map (c :: ·)
  | _ :: _, _, 0 => none
  | c :: cs, tail, n + 1 => (slots cs tail n).map (c :: ·)

theorem align_eq_zip {α : Type} : ∀ (cs : List Codec) (tail : Option Codec) (xs : List α),
    align cs tail xs = (slots cs tail xs.length).map (·.zip xs)
  | [], tail, [] => by cases tail <;> rfl
  | [], none, _ :: _ => rfl
  | [], some c, x :: xs => by
      show (align [] (some c) xs).map ((c, x) :: ·) = _
      rw [align_eq_zip [] (some c) xs]
      cases hs : slots [] (some c) xs.length <;> simp [slots, hs, List.zip]
  | _ :: _, tail, [] => by cases tail <;> rfl
  | c :: cs, tail, x :: xs => by
      show (align cs tail xs).map ((c, x) :: ·) = _
      rw [align_eq_zip cs tail xs]
      cases hs : slots cs tail xs.length <;> simp [slots, hs, List.zip]

theorem slots_length : ∀ (cs : List Codec) (tail : Option Codec) (n : Nat) (ds),
    slots cs tail n = some ds → ds.length = n
  | [], tail, 0, _, h => by cases tail <;> (simp [slots] at h; simp [← h])
  | [], some c, n + 1, ds, h => by
      obtain ⟨ds', h', rfl⟩ := Option.map_eq_some'.mp h
      simp [slots_length [] (some c) n ds' h']
  | c :: cs, tail, n + 1, ds, h => by
      obtain ⟨ds', h', rfl⟩ := Option.map_eq_some'.mp h
      simp [slots_length cs tail n ds' h']

/-- Every codec in the row is one the shape declared. -/
theorem slots_mem : ∀ (cs : List Codec) (tail : Option Codec) (n : Nat) (ds),
    slots cs tail n = some ds → ∀ c ∈ ds, c ∈ cs ∨ tail = some c
  | [], tail, 0, _, h, _, hm => by
      cases tail <;> (simp [slots] at h; subst h; exact nomatch hm)
  | [], some c, n + 1, ds, h, d, hm => by
      obtain ⟨ds', h', rfl⟩ := Option.map_eq_some'.mp h
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact .inr rfl
      · exact slots_mem [] (some c) n ds' h' d hm'
  | c :: cs, tail, n + 1, ds, h, d, hm => by
      obtain ⟨ds', h', rfl⟩ := Option.map_eq_some'.mp h
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact .inl (List.mem_cons_self _ _)
      · exact (slots_mem cs tail n ds' h' d hm').imp (List.mem_cons_of_mem _) id

/-- A property of the shape's codecs is a property of every codec in every row. -/
theorem slots_all {Q : Codec → Prop} {cs : List Codec} {tail : Option Codec}
    (hcs : ∀ c ∈ cs, Q c) (htl : ∀ c ∈ tail, Q c) {n ds}
    (hs : slots cs tail n = some ds) : ∀ c ∈ ds, Q c := fun c hc =>
  (slots_mem cs tail n ds hs c hc).elim (hcs c) (htl c)

/-- **The pivot for `align`.** An alignment is the codec row zipped with the row: which
    codec a position gets depends on the position alone, never on what stands there. -/
theorem align_eq_some {α : Type} {cs : List Codec} {tail : Option Codec}
    {xs : List α} {ps} :
    align cs tail xs = some ps ↔
      ∃ ds, slots cs tail xs.length = some ds ∧ ds.length = xs.length ∧ ps = ds.zip xs := by
  rw [align_eq_zip]
  constructor
  · intro h
    obtain ⟨ds, h', rfl⟩ := Option.map_eq_some'.mp h
    exact ⟨ds, h', slots_length _ _ _ _ h', rfl⟩
  · rintro ⟨ds, h', _, rfl⟩
    rw [h']; rfl

/-- …so any row of the same length aligns against the same codecs. -/
theorem align_of_slots {α : Type} {cs : List Codec} {tail : Option Codec} {n ds}
    (h : slots cs tail n = some ds) {xs : List α} (hn : xs.length = n) :
    align cs tail xs = some (ds.zip xs) := by
  rw [align_eq_zip, hn, h]; rfl

/-! #### §2's clauses, position by position over the codec row -/

theorem zip_roundTrip : ∀ (ds : List Codec) (vs : List Value) (as : List Attr),
    (∀ c ∈ ds, LawfulCore c) → ds.length = vs.length →
    traverse (fun cv : Codec × Value => cv.1.e cv.2) (ds.zip vs) = some as →
    traverse (fun ca : Codec × Attr => ca.1.p ca.2) (ds.zip as) = some vs
  | [], vs, as, _, hlen, h => by simp_all [List.eq_nil_of_length_eq_zero hlen.symm]
  | _ :: _, [], as, _, hlen, h => by simp_all
  | d :: ds, v :: vs, as, hd, hlen, h => by
      rw [List.zip_cons_cons, traverse_cons] at h
      obtain ⟨a, ha, has⟩ := Option.bind_eq_some.mp h
      obtain ⟨as', has', rfl⟩ := Option.map_eq_some'.mp has
      rw [List.zip_cons_cons, traverse_cons, (hd d (by simp)).retract ha,
        zip_roundTrip ds vs as' (fun c hc => hd c (by simp [hc])) (by simpa using hlen) has']
      rfl

theorem zip_canon : ∀ (ds : List Codec) (as : List Attr) (vs : List Value),
    (∀ c ∈ ds, LawfulCore c) →
    traverse (fun ca : Codec × Attr => ca.1.p ca.2) (ds.zip as) = some vs →
    (traverse (fun cv : Codec × Value => cv.1.e cv.2) (ds.zip vs)).isSome
  | [], as, vs, _, h => by simp_all
  | _ :: _, [], vs, _, h => by simp_all
  | d :: ds, a :: as, vs, hd, h => by
      rw [List.zip_cons_cons, traverse_cons] at h
      obtain ⟨v, hv, hvs⟩ := Option.bind_eq_some.mp h
      obtain ⟨vs', hvs', rfl⟩ := Option.map_eq_some'.mp hvs
      obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp ((hd d (by simp)).canon hv)
      obtain ⟨as', has'⟩ := Option.isSome_iff_exists.mp
        (zip_canon ds as vs' (fun c hc => hd c (by simp [hc])) hvs')
      simp [List.zip_cons_cons, traverse_cons, ha', has']

theorem zip_agree : ∀ (ds : List Codec) (as : List Attr) (vs : List Value) (as' : List Attr),
    (∀ c ∈ ds, Lawful c) →
    traverse (fun ca : Codec × Attr => ca.1.p ca.2) (ds.zip as) = some vs →
    traverse (fun cv : Codec × Value => cv.1.e cv.2) (ds.zip vs) = some as' →
    ∀ q ∈ as'.zip as, Agree q.1 q.2
  | [], as, vs, as', _, h, h' => by simp_all
  | _ :: _, [], vs, as', _, h, h' => by simp_all
  | d :: ds, a :: as, vs, as', hd, h, h' => by
      rw [List.zip_cons_cons, traverse_cons] at h
      obtain ⟨v, hv, hvs⟩ := Option.bind_eq_some.mp h
      obtain ⟨vs', hvs', rfl⟩ := Option.map_eq_some'.mp hvs
      rw [List.zip_cons_cons, traverse_cons] at h'
      obtain ⟨a₁, ha₁, has⟩ := Option.bind_eq_some.mp h'
      obtain ⟨as₁, has₁, rfl⟩ := Option.map_eq_some'.mp has
      intro q hq
      rcases List.mem_cons.mp (by simpa using hq) with rfl | hq'
      · exact (hd d (by simp)).agree hv ha₁
      · exact zip_agree ds as vs' as₁ (fun c hc => hd c (by simp [hc])) hvs' has₁ q hq'

/-- Writing a row puts every position on its own carrier… -/
theorem zip_domE : ∀ (ds : List Codec) (vs : List Value) (as : List Attr),
    (∀ c ∈ ds, Carrier c) →
    traverse (fun cv : Codec × Value => cv.1.e cv.2) (ds.zip vs) = some as →
    ∀ q ∈ ds.zip vs, q.1.T q.2
  | [], vs, as, _, h => by simp_all
  | _ :: _, [], as, _, h => by simp_all
  | d :: ds, v :: vs, as, hd, h => by
      rw [List.zip_cons_cons, traverse_cons] at h
      obtain ⟨a, ha, has⟩ := Option.bind_eq_some.mp h
      obtain ⟨as', has', rfl⟩ := Option.map_eq_some'.mp has
      intro q hq
      rcases List.mem_cons.mp (by simpa using hq) with rfl | hq'
      · exact (hd d (by simp)).domE ha
      · exact zip_domE ds vs as' (fun c hc => hd c (by simp [hc])) has' q hq'

/-- …and so does reading one. -/
theorem zip_ranP : ∀ (ds : List Codec) (as : List Attr) (vs : List Value),
    (∀ c ∈ ds, Carrier c) →
    traverse (fun ca : Codec × Attr => ca.1.p ca.2) (ds.zip as) = some vs →
    ∀ q ∈ ds.zip vs, q.1.T q.2
  | [], as, vs, _, h => by simp_all
  | _ :: _, [], vs, _, h => by simp_all
  | d :: ds, a :: as, vs, hd, h => by
      rw [List.zip_cons_cons, traverse_cons] at h
      obtain ⟨v, hv, hvs⟩ := Option.bind_eq_some.mp h
      obtain ⟨vs', hvs', rfl⟩ := Option.map_eq_some'.mp hvs
      intro q hq
      rcases List.mem_cons.mp (by simpa using hq) with rfl | hq'
      · exact (hd d (by simp)).ranP hv
      · exact zip_ranP ds as vs' (fun c hc => hd c (by simp [hc])) hvs' q hq'

/-! #### `tuple` is `carriedCodec` at that pair -/

section Tuple
variable {cs : List Codec} {tail : Option Codec}

theorem tupleCodec_eq :
    tupleCodec cs tail = carriedCodec arrV lA .L
      (fun vs => ∃ ps, align cs tail vs = some ps ∧ ∀ p ∈ ps, p.1.T p.2)
      (fun vs => (align cs tail vs).bind (traverse fun cv => cv.1.e cv.2))
      (fun as => (align cs tail as).bind (traverse fun ca => ca.1.p ca.2)) := by
  refine Codec.ext ?_ rfl ?_ ?_ <;> funext v <;> cases v <;>
    simp [tupleCodec, carriedCodec, arrV, lA, Ctor.into, Ctor.out]

/-- (R) for the payload pair: realign the written row against the same codecs, then
    read back position by position. -/
theorem tuple_retract (hd : ∀ c ∈ cs, LawfulCore c) (htl : ∀ c ∈ tail, LawfulCore c) :
    ∀ vs as, (align cs tail vs).bind (traverse fun cv => cv.1.e cv.2) = some as →
      (align cs tail as).bind (traverse fun ca => ca.1.p ca.2) = some vs := by
  intro vs as hE
  obtain ⟨ps, hal, htr⟩ := Option.bind_eq_some.mp hE
  obtain ⟨ds, hs, hlen, rfl⟩ := align_eq_some.mp hal
  have hn : as.length = vs.length := by
    rw [← traverse_length _ _ htr, List.length_zip, hlen, Nat.min_self]
  exact Option.bind_eq_some.mpr ⟨_, align_of_slots hs hn,
    zip_roundTrip ds vs as (slots_all hd htl hs) hlen htr⟩

/-- (C) for the payload pair, the same way round. -/
theorem tuple_canon (hd : ∀ c ∈ cs, LawfulCore c) (htl : ∀ c ∈ tail, LawfulCore c) :
    ∀ as vs, (align cs tail as).bind (traverse fun ca => ca.1.p ca.2) = some vs →
      ((align cs tail vs).bind (traverse fun cv => cv.1.e cv.2)).isSome := by
  intro as vs hD
  obtain ⟨ps, hal, htr⟩ := Option.bind_eq_some.mp hD
  obtain ⟨ds, hs, hlen, rfl⟩ := align_eq_some.mp hal
  have hn : vs.length = as.length := by
    rw [← traverse_length _ _ htr, List.length_zip, hlen, Nat.min_self]
  rw [align_of_slots hs hn]
  exact zip_canon ds as vs (slots_all hd htl hs) htr

theorem lawfulCore_tupleCodec (hcs : ∀ c ∈ cs, LawfulCore c)
    (htl : ∀ c ∈ tail, LawfulCore c) : LawfulCore (tupleCodec cs tail) :=
  tupleCodec_eq ▸ lawfulCore_carried (fun _ => rfl) (tuple_retract hcs htl)
    (tuple_canon hcs htl)

/-- `≼` at `L` is positional, and so is the alignment — which is why the re-encoded row
    lands on the same codecs and agrees with the stored one entry for entry. -/
theorem lawful_tupleCodec (hcs : ∀ c ∈ cs, Lawful c) (htl : ∀ c ∈ tail, Lawful c) :
    Lawful (tupleCodec cs tail) := by
  refine tupleCodec_eq ▸ lawful_carried (fun _ => rfl)
    (tuple_retract (fun c h => (hcs c h).core) (fun c h => (htl c h).core))
    (tuple_canon (fun c h => (hcs c h).core) (fun c h => (htl c h).core)) ?_
  intro as vs as' hD hE
  obtain ⟨ps, hal, htr⟩ := Option.bind_eq_some.mp hD
  obtain ⟨ds, hs, hlen, rfl⟩ := align_eq_some.mp hal
  have hn : vs.length = as.length := by
    rw [← traverse_length _ _ htr, List.length_zip, hlen, Nat.min_self]
  obtain ⟨ps', hal', htr'⟩ := Option.bind_eq_some.mp hE
  rw [align_of_slots hs hn] at hal'
  cases hal'
  exact .l as' as (zip_agree ds as vs as' (slots_all hcs htl hs) htr htr')

theorem carrier_tupleCodec (hcs : ∀ c ∈ cs, Carrier c) (htl : ∀ c ∈ tail, Carrier c) :
    Carrier (tupleCodec cs tail) := by
  refine tupleCodec_eq ▸ carrier_carried ?_ ?_
  · intro vs as hE
    obtain ⟨ps, hal, htr⟩ := Option.bind_eq_some.mp hE
    obtain ⟨ds, hs, hlen, rfl⟩ := align_eq_some.mp hal
    exact ⟨_, hal, zip_domE ds vs as (slots_all hcs htl hs) htr⟩
  · intro as vs hD
    obtain ⟨ps, hal, htr⟩ := Option.bind_eq_some.mp hD
    obtain ⟨ds, hs, hlen, rfl⟩ := align_eq_some.mp hal
    have hn : vs.length = as.length := by
      rw [← traverse_length _ _ htr, List.length_zip, hlen, Nat.min_self]
    exact ⟨_, align_of_slots hs hn, zip_ranP ds as vs (slots_all hcs htl hs) htr⟩

end Tuple

/-! ## Objects (§4) -/

/-- A field, denoted: presence marker plus the attribute pair. -/
inductive FieldSem where
  | req (c : Codec)
  | opt (c : Codec)
  | fb  (c : Codec) (v : Value)

def FieldSem.codec : FieldSem → Codec
  | .req c => c
  | .opt c => c
  | .fb c _ => c

/-- A rest policy, denoted. -/
inductive RestSem where
  | drop | refuse
  | codec (c : Codec)

/-! ### The field table is a map, not a row

§4 declares a *set* of field names, each with one field — so the table is a `MapOf`,
exactly as `M`'s payload is, and for the same reason. A `List (Name × FieldSem)` admits
two orderings of one object and a repeated name, and the `Nodup` premise that used to
travel with every object law existed to make the first harmless and rule out the second.
Both are now properties of the type, and that premise is gone from all five of them.

`MapOf.at` is the lookup a `MapOf` has: a membership decision and a function application.
It is deliberately shaped like `List.lookup` so that everything downstream — `entryCodec`,
`objEntryT`, `fbValue`, `keepB` and every proof that splits on them — reads unchanged. -/

/-- The value a `MapOf` gives a name, where it gives one — the lookup a key set with a
    function on it has. Generic because the *term*'s field table needs it too. -/
def MapOf.at {α : Type} (m : MapOf α) (k : Name) : Option α :=
  if h : k ∈ m.1 then some (m.2 ⟨k, h⟩) else none

/-- A declared name is one the table's key set carries, and conversely. -/
theorem MapOf.at_eq_some {α : Type} {m : MapOf α} {k : Name} {x : α} :
    m.at k = some x ↔ ∃ h : k ∈ m.1, m.2 ⟨k, h⟩ = x := by
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

/-- `fb`'s absent case, `p♭(ε) = v(∗)`: the stand-ins for the fallback names a row
    omits. Empty on canonical items, where every `fb` name is present.

    A `Finset.filter` over the declared names, where the list form was a fold with an
    `insert` — and its characterization is `Finset.mem_filter` rather than an induction. -/
def isFbB : Option FieldSem → Bool
  | some (.fb _ _) => true
  | _ => false

def fbNames (names : Finset Name) (sems : MapOf FieldSem) : Finset Name :=
  sems.1.filter fun k => isFbB (sems.at k) && !decide (k ∈ names)

/-- …and the stand-in each of them reads to. -/
def fbValue (sems : MapOf FieldSem) (k : Name) : Option Value :=
  match sems.at k with
  | some (.fb _ v) => some v
  | _ => none

/-- What each guard asks of one binding, named so the guards themselves are a single
    quantifier over the key set rather than a `List.all` over a row. -/
def valPresentAt (names : Finset Name) : Name → FieldSem → Bool
  | _, .opt _ => true
  | k, _ => decide (k ∈ names)

def reqPresentAt (names : Finset Name) : Name → FieldSem → Bool
  | k, .req _ => decide (k ∈ names)
  | _, _ => true

/-- Every non-`opt` binding present — the value-side guard (§4: `fallback` concludes
    `req`). -/
def valPresentB (sems : MapOf FieldSem) (names : Finset Name) : Bool :=
  decide (∀ k : {k // k ∈ sems.1}, valPresentAt names k.1 (sems.2 k) = true)

/-- Every `req` name present — the stored-side guard; `fb` reads to its stand-in. -/
def reqPresentB (sems : MapOf FieldSem) (names : Finset Name) : Bool :=
  decide (∀ k : {k // k ∈ sems.1}, reqPresentAt names k.1 (sems.2 k) = true)

/-- The rest policy's codec, where it has one. -/
def rcOf : RestSem → Option Codec
  | .codec c => some c
  | _ => none

/-- The name filter: `drop` keeps declared names only; the others keep everything.
    A filter, never a traversal mode (§4). -/
def keepB (rest : RestSem) (sems : MapOf FieldSem) : Name → Bool :=
  match rest with
  | .drop => fun k => (sems.at k).isSome
  | _ => fun _ => true

/-! ### The object, taken apart

Three namings, and everything §4 asks becomes short. **`entryCodec`** is the codec one
entry goes through — the field its name declares, or else the rest policy's — which is
the only thing ~~encEntry~~/~~decEntry~~ do with a name, so every per-entry law is one appeal
to `entryCodec_of`. **`objWrite`/`objRead`** are the payload pair: the guard and the
steps going out, the guard, the `drop` filter, the steps and the fallback stand-ins
coming back. **`objectCodecCore_eq`** then makes the object `carriedCodec` between `map`
and `M`, so §2's prism halves are the ones already discharged. -/

/-- The per-name half of §4's held set: a declared name holds its field's set, an
    undeclared one falls to the open part `R(ρ)`. -/
def objEntryT (sems : MapOf FieldSem) (rc? : Option Codec) :
    Name × Value → Prop := fun kv =>
  match sems.at kv.1 with
  | some fs => fs.codec.T kv.2
  | none => ∃ rc, rc? = some rc ∧ rc.T kv.2

/-- The codec one entry goes through: the field its name declares, or else the rest
    policy's. `none` is an undeclared name under `refuse`. -/
def entryCodec (sems : MapOf FieldSem) (rc? : Option Codec) (k : Name) :
    Option Codec :=
  match sems.at k with
  | some fs => some fs.codec
  | none => rc?

section Object
variable {sems : MapOf FieldSem} {rc? : Option Codec} {kn : Name → Bool}

/-- A property of every field and of the rest codec is a property of every entry's
    codec — which is how the object's per-entry laws are discharged, once each. -/
theorem entryCodec_of {Q : Codec → Prop} (hf : ∀ k, Q (sems.2 k).codec)
    (hrc : ∀ c ∈ rc?, Q c) {k c} (h : entryCodec sems rc? k = some c) : Q c := by
  simp only [entryCodec] at h
  cases hsp : sems.at k with
  | some fs => rw [hsp] at h; cases h; exact MapOf.at_forall (Q := fun fs => Q fs.codec) hf hsp
  | none => rw [hsp] at h; exact hrc c h



/-- §4's held set, per entry, in the same vocabulary. -/
theorem objEntryT_eq {kv} :
    objEntryT sems rc? kv ↔ ∃ c, entryCodec sems rc? kv.1 = some c ∧ c.T kv.2 := by
  simp only [objEntryT, entryCodec]
  cases sems.at kv.1 <;> simp

/-- The object's payload pair, going out: the value-side presence guard, then the
    name-dispatched steps. -/
noncomputable def objWrite (sems : MapOf FieldSem) (rc? : Option Codec) :
    MapOf Value → Option (MapOf Attr) := fun p =>
  if valPresentB sems p.1 = true then
    (funImage (fun k => (entryCodec sems rc? k.1).bind (fun c => c.e (p.2 k)))).map
      (fun g => ⟨p.1, g⟩)
  else none

/-- …and coming back: the stored-side guard, the `drop` filter, the steps, and the
    stand-ins for the fallback names the row omits. -/
noncomputable def objRead (sems : MapOf FieldSem) (rc? : Option Codec)
    (kn : Name → Bool) : MapOf Attr → Option (MapOf Value) := fun p =>
  if reqPresentB sems p.1 = true then
    (funImage (fun k : {k // k ∈ p.1.filter (kn ·)} =>
        (entryCodec sems rc? k.1).bind
          (fun c => c.p (p.2 ⟨k.1, (Finset.mem_filter.mp k.2).1⟩)))).map
      (fun d => ⟨p.1.filter (kn ·) ∪ fbNames p.1 sems, fun k =>
        if h : k.1 ∈ p.1.filter (kn ·) then d ⟨k.1, h⟩
        else (fbValue sems k.1).getD .null⟩)
  else none

theorem objWrite_eq {p : MapOf Value} {q : MapOf Attr} :
    objWrite sems rc? p = some q ↔
      valPresentB sems p.1 = true ∧ ∃ g,
        funImage (fun k => (entryCodec sems rc? k.1).bind (fun c => c.e (p.2 k))) = some g ∧
        q = ⟨p.1, g⟩ := by
  simp only [objWrite]
  split
  · next hg => simp [hg, Option.map_eq_some', eq_comm (a := q)]
  · next hg => simp [hg]

theorem objRead_eq {q : MapOf Attr} {p : MapOf Value} :
    objRead sems rc? kn q = some p ↔
      reqPresentB sems q.1 = true ∧ ∃ d,
        funImage (fun k : {k // k ∈ q.1.filter (kn ·)} =>
            (entryCodec sems rc? k.1).bind
              (fun c => c.p (q.2 ⟨k.1, (Finset.mem_filter.mp k.2).1⟩))) = some d ∧
        p = ⟨q.1.filter (kn ·) ∪ fbNames q.1 sems, fun k =>
              if h : k.1 ∈ q.1.filter (kn ·) then d ⟨k.1, h⟩
              else (fbValue sems k.1).getD .null⟩ := by
  simp only [objRead]
  split
  · next hg => simp [hg, Option.map_eq_some', eq_comm (a := p)]
  · next hg => simp [hg]

/-- The object is `carriedCodec` between `map` and `M`, at that pair. -/
noncomputable def objectCodecCore (sems : MapOf FieldSem) (rc? : Option Codec)
    (kn : Name → Bool) : Codec :=
  carriedCodec mapV mA .M
    (fun p => valPresentB sems p.1 = true ∧ ∀ k, objEntryT sems rc? (k.1, p.2 k))
    (objWrite sems rc?) (objRead sems rc? kn)

noncomputable def objectCodec (sems : MapOf FieldSem) (rest : RestSem) : Codec :=
  objectCodecCore sems (rcOf rest) (keepB rest sems)

theorem objectCodecCore_eq :
    objectCodecCore sems rc? kn =
      carriedCodec mapV mA .M
        (fun p => valPresentB sems p.1 = true ∧ ∀ k, objEntryT sems rc? (k.1, p.2 k))
        (objWrite sems rc?) (objRead sems rc? kn) := rfl

/-- Inversion of an object-encode success: the value is a map, the guard held, and the
    written item is the entrywise traversal. -/
theorem objectCodecCore_e_inv {t a} (he : (objectCodecCore sems rc? kn).e t = some a) :
    ∃ keys f g, t = Value.map keys f ∧ a = Attr.m keys g ∧
      valPresentB sems keys = true ∧
      funImage (fun k => (entryCodec sems rc? k.1).bind (fun c => c.e (f k))) = some g := by
  obtain ⟨p, q, hv, hw, rfl⟩ := carried_e.mp (objectCodecCore_eq ▸ he)
  obtain ⟨hval, g, hg, rfl⟩ := objWrite_eq.mp hw
  exact ⟨p.1, p.2, g, mapV.into_out hv, rfl, hval, hg⟩

end Object

/-! ## Sums (§5): admission as data -/

/-- One union option: its admission functions and its pair. The doc's `κ`/`ident`/name
    devices become *builders* of these. -/
structure OptionSem where
  admitA : Attr → Bool
  admitV : Value → Bool
  c : Codec

/-- Name admission (objects): every present name declared, every required name present.
    The spec is a `MapOf Bool` — the declared names with each one's required flag —
    for the same reason the field table is: a list of pairs admits orderings and
    repeats that a declaration does not have. -/
def keysOk (spec : MapOf Bool) (keys : Finset Name) : Bool :=
  decide (∀ k ∈ keys, k ∈ spec.1) &&
  decide (∀ k : {k // k ∈ spec.1}, spec.2 k = true → k.1 ∈ keys)

/-- An object option decides by names, never by being attempted. -/
def OptionSem.byNames (spec : MapOf Bool) (c : Codec) : OptionSem :=
  { admitA := fun a => match a with | .m keys _ => keysOk spec keys | _ => false
    admitV := fun v => match v with | .map keys _ => keysOk spec keys | _ => false
    c := c }

/-- Any other option is admitted by attempt — the doc's `ident` caveat lives in the
    (U) premise, not here. -/
def OptionSem.byAttempt (c : Codec) : OptionSem :=
  { admitA := fun a => (c.p a).isSome
    admitV := fun v => (c.e v).isSome
    c := c }

/-- An attempted option admits an attribute exactly when its `p` is defined there — the
    §1 rule applied to admission, so no proof takes `byAttempt` apart by hand. -/
@[simp] theorem OptionSem.byAttempt_admitA {c : Codec} {a : Attr} :
    (OptionSem.byAttempt c).admitA a = (c.p a).isSome := rfl

/-- …and a value exactly when its `e` is. -/
@[simp] theorem OptionSem.byAttempt_admitV {c : Codec} {v : Value} :
    (OptionSem.byAttempt c).admitV v = (c.e v).isSome := rfl

/-- The `⟨NULL⟩` point as a union option — §3's second half of `nullable(c)` read as
    `union(c, ⟨NULL⟩-point)`. It decides by attempting, like any ground option. -/
abbrev nullOption : OptionSem := .byAttempt nullCodec

/-- §5's discriminator projection: the tag an item carries at `d`, where it carries one.
    A membership decision and a function application, where the list representation needed
    a `lookup`. -/
def tagOfV (d : Name) : Value → Option String
  | .map keys f =>
    if h : d ∈ keys then (match f ⟨d, h⟩ with | .str s => some s | _ => none) else none
  | _ => none

/-- …and on the stored side. -/
def tagOfA (d : Name) : Attr → Option String
  | .m keys g =>
    if h : d ∈ keys then (match g ⟨d, h⟩ with | .s s => some s | _ => none) else none
  | _ => none

/-- A `(dunion)` option is admitted by its discriminator tag. -/
def OptionSem.byTag (d : Name) (tags : Finset String) (c : Codec) : OptionSem :=
  { admitA := fun a => match tagOfA d a with | some tag => decide (tag ∈ tags) | none => false
    admitV := fun v => match tagOfV d v with | some tag => decide (tag ∈ tags) | none => false
    c := c }

/-- A tag option admits exactly the items whose discriminator carries one of its tags. -/
theorem byTag_admitA {d : Name} {tags : Finset String} {c : Codec} {a : Attr} :
    (OptionSem.byTag d tags c).admitA a = true ↔
      ∃ tag, tagOfA d a = some tag ∧ tag ∈ tags := by
  simp only [OptionSem.byTag]
  cases h : tagOfA d a with
  | none => simp
  | some tag => simp

/-- …and the values whose discriminator carries one, on the way in. -/
theorem byTag_admitV {d : Name} {tags : Finset String} {c : Codec} {v : Value} :
    (OptionSem.byTag d tags c).admitV v = true ↔
      ∃ tag, tagOfV d v = some tag ∧ tag ∈ tags := by
  simp only [OptionSem.byTag]
  cases h : tagOfV d v with
  | none => simp
  | some tag => simp

/-- The builder `denote` uses for a union option. -/
def optionSemOf (c : Codec) : Option (MapOf Bool) → OptionSem
  | some spec => .byNames spec c
  | none => .byAttempt c

/-- §5 (U) at every option's canonical pairs: each is admitted by that option alone, on
    both sides. The strong form, and what every discharger in `Discharge` produces. -/
def UniqueAdmission (os : List OptionSem) : Prop :=
  ∀ o ∈ os, ∀ t a, o.c.e t = some a →
    os.filter (·.admitA a) = [o] ∧ os.filter (·.admitV t) = [o]

/-- **§5 (U) where the laws consume it**, and the soundness theorem's actual residue.

    `UniqueAdmission` quantifies over every canonical pair of every *option*. The four
    laws never ask that much: they ask only about inputs the *union itself* resolves,
    because `altCodec` is undefined wherever the filter is not a singleton, and a law
    quantified over `dom` cannot reach an input the pair declines. This is that
    restriction — resolving one side of the pair resolves the other, through the same
    option — and the three uses in `lawfulCore_altCodec` and `lawful_altCodec` are
    exactly its two clauses.

    Strictly weaker, and the gap holds working schemas.
    `union(array(literal "A"), array(literal "B"))` collides at `[]`, which is a
    canonical pair of each option and so refutes `UniqueAdmission`
    (`not_uAtCan_array_literals`) — while the union declines to write `[]` at all, so it
    never acts there and no law is ever asked. `adm` stops at the containers (§5), which
    is why the collision is the empty case and nothing else. `uAtAct_array_literals` is
    that union meeting this condition, so the two are separated by a theorem and not by
    an argument. -/
def UniqueBothWays (os : List OptionSem) : Prop :=
  (∀ o ∈ os, ∀ t a, os.filter (·.admitV t) = [o] → o.c.e t = some a →
    os.filter (·.admitA a) = [o]) ∧
  (∀ o ∈ os, ∀ a t a', os.filter (·.admitA a) = [o] → o.c.p a = some t →
    o.c.e t = some a' → os.filter (·.admitV t) = [o])

/-- The strong form implies the one the laws need — so every discharger still discharges,
    unchanged. The converse fails, which is the whole point. -/
theorem uniqueBothWays_of_uniqueAdmission {os : List OptionSem}
    (hU : UniqueAdmission os) : UniqueBothWays os :=
  ⟨fun o ho t a _ he => (hU o ho t a he).1,
   fun o ho _ t a' _ _ he => (hU o ho t a' he).2⟩

/-- A union's member: `μ` when unanimous, else `⊤` (§5 `(union)`). -/
def unanimous : List (Option Member) → Option Member
  | [] => none
  | μ :: μs => if μs.all (· == μ) then μ else none

/-- **One side of a sum.** Both halves of `altCodec` are this: filter the options by the
    admission *that side* reads, and act through the one that answers alone. The two
    differ only in which admission and which half of the pair — so stating the shape once
    is what lets `altCodec_e` and `altCodec_p` be the same theorem at two instances,
    instead of one theorem written twice. -/
def select {A B : Type} (os : List OptionSem) (adm : OptionSem → A → Bool)
    (run : OptionSem → A → Option B) (x : A) : Option B :=
  match os.filter (adm · x) with
  | [o] => run o x
  | _ => none

/-- `union`: the sum, resolved by unique admission — never by declaration order. -/
def altCodec (os : List OptionSem) (μA : Option Member) : Codec :=
  { T := fun v => ∃ o ∈ os, o.c.T v
    μ := μA
    e := select os (·.admitV) (·.c.e)
    p := select os (·.admitA) (·.c.p) }

/-- `discriminatedUnion` is not its own codec: it is the sum over tag-admission
    options. Its (U) is `uniqueAdmission_byTag` — a theorem, which is what the term
    is for. -/
def dunionCodec (d : Name) (os : List (Finset String × Codec)) : Codec :=
  altCodec (os.map fun o => .byTag d o.1 o.2) (some .M)

/-! ## Unknown values (§3 `(opaque)`) -/

/-- §3 `(opaque)`'s eight self-identifying options; `rec` is where the recursion goes.

    Named because three statements cite it — `opaqCodec`, `opaq_onKinds`,
    `uniqueAdmission_opaque` — and a list spelled three times can drift twice. **`refuse` is
    the absence of an option**, spelled here as the empty codec. -/
def opaqOptions (lossy : Bool) (rec : Codec) : List OptionSem :=
  [.byAttempt stringCodec, .byAttempt booleanCodec, .byAttempt binaryCodec,
   .byAttempt nullCodec,
   .byAttempt (if lossy then numberCodec else Codec.empty),
   .byAttempt (setCodec rec), .byAttempt (arrayCodec rec), .byAttempt (recordCodec rec)]

/-- `opaque` is not special: it is the recursive union of everything self-identifying,
    closed under the containers — "the values whose type is recoverable", as a
    fixpoint of the algebra. Its (U) is kind-disjointness (`uniqueAdmission_opaque`,
    via `uniqueAdmission_of_kinds`). -/
def opaqCodec : Nat → Bool → Codec
  | 0, _ => .empty
  | fuel+1, lossy => altCodec (opaqOptions lossy (opaqCodec fuel lossy)) none

/-! ## Carriers — the pair is on `T` (§3 `e : T ⇀ 𝔸`, `p : 𝔸 ⇀ T`)

    One `Carrier` lemma per combinator, mirroring the lawfulness lemmas below. Together
    with `typed_TSub` (Soundness.lean) these make the judgement's held-set index a
    checked claim: what a derivable term writes and reads lies in the `T` it names. -/


/-- The carrier, likewise: `e` only writes what `V` matched, `p` only reads what `V`
    built. -/
theorem carrier_pointCodec {α : Type} {V : Ctor α Value} {A : Ctor α Attr} {μ₀ : Member} :
    Carrier (pointCodec V A μ₀) := by
  refine ⟨?_, ?_⟩
  · intro v a h
    obtain ⟨x, hx, _⟩ := Option.map_eq_some'.mp h
    exact ⟨x, V.into_out hx⟩
  · intro a v h
    obtain ⟨x, _, rfl⟩ := Option.map_eq_some'.mp h
    exact ⟨x, rfl⟩

/-- The four point ground codecs are on their carriers for one reason, the same one that
    made them lawful: `e` only writes what the value prism matched, and `p` only reads what
    it built. See `carrier_pointCodec`. -/
theorem carrier_stringCodec : Carrier stringCodec :=
  Carrier.congr (d := pointCodec strV sC .S)
    (by funext v; cases v <;> rfl) (by funext a; cases a <;> rfl)
    (fun _ h => h) carrier_pointCodec

theorem carrier_decimalCodec : Carrier decimalCodec := by
  refine ⟨?_, ?_⟩
  · intro v a h
    cases v with
    | str s =>
      replace h : (if hh : Numeral.Stored s = true then some (Attr.n ⟨s, Numeral.stored_wf hh⟩) else none) = some a := h
      by_cases hw : Numeral.Stored s = true
      · exact ⟨s, rfl, hw⟩
      · rw [dif_neg hw] at h; exact nomatch h
    | _ => exact nomatch h
  · intro a v h
    cases a with
    | n x =>
      replace h : (if Numeral.Stored x.1 = true then some (Value.str x.1) else none) = some v := h
      by_cases hw : Numeral.Stored x.1 = true
      · rw [if_pos hw] at h; cases h; exact ⟨x.1, rfl, hw⟩
      · rw [if_neg hw] at h; exact nomatch h
    | _ => exact nomatch h

theorem carrier_booleanCodec : Carrier booleanCodec :=
  Carrier.congr (d := pointCodec boolV boolA .BOOL)
    (by funext v; cases v <;> rfl) (by funext a; cases a <;> rfl)
    (fun _ h => h) carrier_pointCodec

theorem carrier_binaryCodec : Carrier binaryCodec :=
  Carrier.congr (d := pointCodec binV bC .B)
    (by funext v; cases v <;> rfl) (by funext a; cases a <;> rfl)
    (fun _ h => h) carrier_pointCodec

theorem carrier_nullCodec : Carrier nullCodec :=
  Carrier.congr (d := pointCodec nullV nullA .NULL)
    (by funext v; cases v <;> rfl) (by funext a; cases a <;> rfl)
    (fun _ h => h.elim fun _ hh => hh) carrier_pointCodec

theorem carrier_numberCodec : Carrier numberCodec := by
  refine ⟨?_, ?_⟩
  · intro v a h
    cases v with
    | num d =>
      rw [numberCodec_e_num] at h
      by_cases hw : Numeral.WF d.toDec = true
      · exact ⟨d, rfl, hw⟩
      · rw [dif_neg hw] at h; exact nomatch h
    | _ => exact nomatch h
  · intro a v h
    cases a with
    | n x =>
      rw [numberCodec_p_n] at h
      cases hd : Double.ofDec x.1 with
      | none => rw [hd] at h; exact nomatch h
      | some d =>
        rw [hd] at h
        replace h : (if Numeral.WF d.toDec then some (Value.num d) else none) = some v := h
        by_cases hw : Numeral.WF d.toDec = true
        · rw [if_pos hw] at h; cases h; exact ⟨d, rfl, hw⟩
        · rw [if_neg hw] at h; exact nomatch h
    | _ => exact nomatch h

/-! ### Sums -/

/-! ### How a union resolves

`altCodec`'s two halves are the same shape: filter the options by admission, and answer
if and only if exactly one survives. Stated as an `iff`, that is the whole of the union
— every theorem about `union` below, and every row of §6 that mentions one, is a
statement about `os.filter` and nothing else. -/

/-- **What a selection produces**: exactly one option admitted, and it answered. -/
theorem select_eq_some {A B : Type} {os : List OptionSem} {adm : OptionSem → A → Bool}
    {run : OptionSem → A → Option B} {x : A} {y : B} :
    select os adm run x = some y ↔ ∃ o, os.filter (adm · x) = [o] ∧ run o x = some y := by
  show (match os.filter (adm · x) with | [o] => run o x | _ => none) = some y ↔ _
  cases hf : os.filter (adm · x) with
  | nil => simp
  | cons o tl => cases tl <;> simp

/-- …and it routes through an option that admits. -/
theorem select_admits {A B : Type} {os : List OptionSem} {adm : OptionSem → A → Bool}
    {run : OptionSem → A → Option B} {x : A} {y : B}
    (h : select os adm run x = some y) : ∃ o ∈ os, adm o x = true ∧ run o x = some y := by
  obtain ⟨o, hf, hr⟩ := select_eq_some.mp h
  obtain ⟨ho, hadm⟩ := mem_of_filter_eq_singleton hf
  exact ⟨o, ho, hadm, hr⟩

/-- **What a union writes**: exactly one option admitted the value, and it wrote. -/
theorem altCodec_e {os : List OptionSem} {μA : Option Member} {v a} :
    (altCodec os μA).e v = some a ↔
      ∃ o, os.filter (·.admitV v) = [o] ∧ o.c.e v = some a := select_eq_some

/-- **What a union reads**: the same theorem, on the attribute side. -/
theorem altCodec_p {os : List OptionSem} {μA : Option Member} {a v} :
    (altCodec os μA).p a = some v ↔
      ∃ o, os.filter (·.admitA a) = [o] ∧ o.c.p a = some v := select_eq_some

/-- A sum's encode routes through an admitting option. -/
theorem altCodec_e_admits {os : List OptionSem} {μA : Option Member} {v a}
    (he : (altCodec os μA).e v = some a) :
    ∃ o ∈ os, o.admitV v = true ∧ o.c.e v = some a := select_admits he

/-- A sum's decode routes through an admitting option — the same theorem again. -/
theorem altCodec_p_admits {os : List OptionSem} {μA : Option Member} {a v}
    (hp : (altCodec os μA).p a = some v) :
    ∃ o ∈ os, o.admitA a = true ∧ o.c.p a = some v := select_admits hp

/-! ### Wrappers -/

theorem carrier_through {c : Codec} {f g : Value → Value} (hc : Carrier c)
    (hlaw : LawfulCore c) (hfg : ∀ v, (c.e v).isSome → f (g v) = v) :
    Carrier (c.through f g) where
  domE he := hc.domE (through_e.mp he)
  ranP hp := by
    obtain ⟨w, hw, rfl⟩ := through_p.mp hp
    show c.T (f (g w))
    rw [hfg w (hlaw.canon hw)]
    exact hc.ranP hw

theorem carrier_restrict {c : Codec} (hc : Carrier c) (q : Value → Bool) :
    Carrier (c.restrict q) where
  domE he := let ⟨hq, hcv⟩ := restrict_e.mp he; ⟨hc.domE hcv, hq⟩
  ranP hp := let ⟨hcv, hq⟩ := restrict_p.mp hp; ⟨hc.ranP hcv, hq⟩


/-- Every base is on its carrier — the six lemmas above, indexed. -/
theorem carrier_baseCodec : ∀ k : GroundKind, Carrier (baseCodec k)
  | .string  => carrier_stringCodec
  | .number  => carrier_numberCodec
  | .decimal => carrier_decimalCodec
  | .boolean => carrier_booleanCodec
  | .binary  => carrier_binaryCodec
  | .null    => carrier_nullCodec

/-- …and each set base's element pair is on its carrier too. -/
theorem carrier_setBase : ∀ b : SetBase, Carrier b.elem
  | .string  => carrier_stringCodec
  | .number  => carrier_numberCodec
  | .decimal => carrier_decimalCodec
  | .binary  => carrier_binaryCodec

/-! ### The refinement ground codecs, on their carriers -/

/-- **One theorem where there were two, and the numeric one was twenty-six lines.**

    ~~literalNCodec~~'s carrier used to be proved by hand — unfolding `Double.ofDec`, splitting on
    `Numeral.WF`, then on membership — because the codec was a hand-written pair that only
    *agreed* with a restriction. It now **is** the restriction, so `carrier_restrict` supplies
    everything and all that remains is the held set being no smaller than the restriction's,
    which is `hLit_of_inL`. -/
theorem carrier_literalCodec (k : GroundKind) (ls : NEFinset k.Carrier) :
    Carrier (literalCodec k ls) :=
  Carrier.congr (d := (baseCodec k).restrict (inL k ls)) rfl rfl
    (fun _ hv => hLit_of_inL k ls _ hv.2)
    (carrier_restrict (carrier_baseCodec k) (inL k ls))

/-- `legacy`: the migration lands in `T` because §3's `ran(r) ⊆ dom(e)` puts it in
    `dom(e)`, and `e`'s domain is `T`. The doc writes `r : 𝔸 ⇀ T` directly; this is the
    same premise arrived at through the one the proof already needs. -/
theorem carrier_extendRead {c : Codec} {r : Attr → Option Value} (hc : Carrier c)
    (hran : ∀ a v, r a = some v → (c.e v).isSome) :
    Carrier (c.extendRead r) where
  domE he := hc.domE (extendRead_e.mp he)
  ranP hp := by
    rcases extendRead_p.mp hp with hcv | ⟨-, hrv⟩
    · exact hc.ranP hcv
    · obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (hran _ _ hrv)
      exact hc.domE ha'

theorem carrier_orNull {c : Codec} (hc : Carrier c) : Carrier c.orNull where
  domE he := by
    rcases orNull_e.mp he with ⟨hv, -⟩ | ⟨-, hcv⟩
    · exact .inr hv
    · exact .inl (hc.domE hcv)
  ranP hp := by
    rcases orNull_p.mp hp with ⟨-, hv⟩ | ⟨-, hcv⟩
    · exact .inr hv
    · exact .inl (hc.ranP hcv)

/-! ### Containers -/


/-- `set`: non-emptiness comes from the codec refusing an empty set on both sides, and
    membership in the held set from the element codec's own carrier. Uniqueness and order
    are no longer conditions at all — the `Finset` carries them. -/
theorem carrier_setCodec {c : Codec} (hc : Carrier c) : Carrier (setCodec c) where
  domE he := by
    rcases setCodec_e_eq.mp he with ⟨S, rfl, hE⟩ | ⟨S, rfl, hE⟩ | ⟨S, rfl, hE⟩ <;>
      refine fun x hx => ?_ <;>
      · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (encSet_elem hE x hx)
        exact hc.domE hb
  ranP hp := by
    rcases setCodec_p_eq.mp hp with ⟨S, rfl, hD⟩ | ⟨S, rfl, hD⟩ | ⟨S, rfl, hD⟩ <;>
      · rcases decSet_mem hD with ⟨T, rfl, hm⟩ | ⟨T, rfl, hm⟩ | ⟨T, rfl, hm⟩ <;>
        · refine fun y hy => ?_
          obtain ⟨x, -, hx⟩ := hm y hy
          exact hc.ranP hx

/-! ### Sums -/

theorem carrier_altCodec {os : List OptionSem} {μA : Option Member}
    (h : ∀ o ∈ os, Carrier o.c) : Carrier (altCodec os μA) := by
  refine ⟨?_, ?_⟩
  · intro v a he
    obtain ⟨o, ho, -, hoe⟩ := altCodec_e_admits he
    exact ⟨o, ho, (h o ho).domE hoe⟩
  · intro a v hp
    obtain ⟨o, ho, -, hop⟩ := altCodec_p_admits hp
    exact ⟨o, ho, (h o ho).ranP hop⟩


/-- `opaque`'s fixpoint is on its carrier at every fuel — §3's `Uν`, one option per
    kind, `refuse` being the absence of the `number` option. -/
theorem carrier_opaqCodec : ∀ (fuel : Nat) (lossy : Bool), Carrier (opaqCodec fuel lossy)
  | 0, _ => Carrier.empty
  | fuel+1, lossy => by
    have ih := carrier_opaqCodec fuel lossy
    refine carrier_altCodec ?_
    intro o ho
    simp only [opaqOptions, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact carrier_stringCodec
    · exact carrier_booleanCodec
    · exact carrier_binaryCodec
    · exact carrier_nullCodec
    · cases lossy with
      | false => exact Carrier.empty
      | true => exact carrier_numberCodec
    · exact carrier_setCodec ih
    · exact carrier_arrayCodec ih
    · exact carrier_recordCodec ih

/-! ## Lawfulness — proved -/

/-! ### The point ground codecs, argued once

`string`, `boolean`, `binary` and `null` are `pointCodec` at four different pairs of
prisms. Below, each of the four is that one lemma transported across the definitional
equality by `Lawful.congr`, which is what lets the definitions stay in the unfolded form
the rest of the development `simp`s with. -/

/-- §2's four laws for any pair of prisms. The two premises are the only things a prism
    pair does not already supply: which member the attribute side stamps, and that `≼` is
    reflexive on its image. Everything else is `out_into` and `into_out`. -/
theorem lawful_pointCodec {α : Type} {V : Ctor α Value} {A : Ctor α Attr} {μ₀ : Member}
    (hμ : ∀ x, (A.into x).member = μ₀) (hrefl : ∀ x, Agree (A.into x) (A.into x)) :
    Lawful (pointCodec V A μ₀) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (R): match, rebuild, match again — `out_into` on each side.
    intro t a he
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some'.mp he
    simp [pointCodec, A.out_into, ← V.into_out hx]
  · -- (C): what `p` produced was built by `V`, so `V.out` matches it.
    intro a t hp
    obtain ⟨x, _, rfl⟩ := Option.map_eq_some'.mp hp
    simp [pointCodec, V.out_into]
  · -- (W): everything written is `A.into` of something.
    intro μ hm t a he
    obtain ⟨x, _, rfl⟩ := Option.map_eq_some'.mp he
    cases hm; exact hμ x
  · -- (MP): the re-encoding is the attribute itself, not merely an agreeing one.
    intro a t a' hp he
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some'.mp hp
    simp only [pointCodec, V.out_into, Option.map_some'] at he
    cases he
    rw [A.into_out hx]
    exact hrefl x

theorem lawful_stringCodec : Lawful stringCodec :=
  Lawful.congr (d := pointCodec strV sC .S)
    (by funext v; cases v <;> rfl) (by funext a; cases a <;> rfl) rfl
    (lawful_pointCodec (fun _ => rfl) (fun _ => .s ..))

theorem lawful_booleanCodec : Lawful booleanCodec :=
  Lawful.congr (d := pointCodec boolV boolA .BOOL)
    (by funext v; cases v <;> rfl) (by funext a; cases a <;> rfl) rfl
    (lawful_pointCodec (fun _ => rfl) (fun _ => .bool ..))

theorem lawful_binaryCodec : Lawful binaryCodec :=
  Lawful.congr (d := pointCodec binV bC .B)
    (by funext v; cases v <;> rfl) (by funext a; cases a <;> rfl) rfl
    (lawful_pointCodec (fun _ => rfl) (fun _ => .b ..))

theorem lawful_nullCodec : Lawful nullCodec :=
  Lawful.congr (d := pointCodec nullV nullA .NULL)
    (by funext v; cases v <;> rfl) (by funext a; cases a <;> rfl) rfl
    (lawful_pointCodec (fun _ => rfl) (fun _ => .null))

/-- `e` and `p` gate on the *same* predicate applied to the *same* text, so each law
    reduces to that one decision. -/
theorem decimalCodec_e_str (s : String) :
    decimalCodec.e (.str s)
      = if h : Numeral.Stored s then some (.n ⟨s, Numeral.stored_wf h⟩) else none := rfl

theorem decimalCodec_p_n (x : WFNumeral) :
    decimalCodec.p (.n x) = if Numeral.Stored x.1 then some (.str x.1) else none := rfl

theorem lawful_decimalCodec : Lawful decimalCodec := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t a he
    cases t with
    | str s =>
      rw [decimalCodec_e_str] at he
      by_cases hw : Numeral.Stored s = true
      · rw [dif_pos hw] at he; cases he; rw [decimalCodec_p_n, if_pos hw]
      · rw [dif_neg hw] at he; exact nomatch he
    | _ => exact nomatch he
  · intro a t hp
    cases a with
    | n x =>
      rw [decimalCodec_p_n] at hp
      by_cases hw : Numeral.Stored x.1 = true
      · rw [if_pos hw] at hp; cases hp; rw [decimalCodec_e_str, dif_pos hw]; rfl
      · rw [if_neg hw] at hp; exact nomatch hp
    | _ => exact nomatch hp
  · intro μ hμ t a he
    cases t with
    | str s =>
      rw [decimalCodec_e_str] at he
      by_cases hw : Numeral.Stored s = true
      · rw [dif_pos hw] at he; cases he; cases hμ; rfl
      · rw [dif_neg hw] at he; exact nomatch he
    | _ => exact nomatch he
  · intro a t a' hp he
    cases a with
    | n x =>
      rw [decimalCodec_p_n] at hp
      by_cases hw : Numeral.Stored x.1 = true
      · rw [if_pos hw] at hp
        cases hp
        rw [decimalCodec_e_str, dif_pos hw] at he
        cases he
        exact .n ..
      · rw [if_neg hw] at hp; exact nomatch hp
    | _ => exact nomatch hp

/-! ### `number` against the store (§1)

The other side of `decimal`'s answer, and the reason §1 states the condition as an inclusion
rather than as an equality. -/

/-- §1: `number` survives the store for free. Its `p` factors through `ofDec`, so the digits
    may be rewritten freely — the contrast with `ker_decimalCodec`, whose kernel is equality. -/
theorem survivesStore_numberCodec {η : Attr → Attr}
    (hη : ∀ x : WFNumeral, ∃ y : WFNumeral, η (.n x) = .n y ∧
      Double.ofDec y.1 = Double.ofDec x.1) :
    SurvivesStore numberCodec η := by
  rintro a ⟨v, hv⟩
  cases v with
  | num d =>
    rw [numberCodec_e_num] at hv
    by_cases hw : Numeral.WF d.toDec = true
    · rw [dif_pos hw] at hv
      cases hv
      obtain ⟨y, hy, hofd⟩ := hη ⟨d.toDec, hw⟩
      show numberCodec.p (η (.n ⟨d.toDec, hw⟩)) = numberCodec.p (.n ⟨d.toDec, hw⟩)
      rw [hy, numberCodec_p_n, numberCodec_p_n, hofd]
    · rw [dif_neg hw] at hv; exact nomatch hv
  | _ => exact nomatch hv

/-! ### `decimal` against the store (§1)

`SurvivesStore` is the premise; these two are `decimal`'s answer to it, and together they say
that narrowing the held set to `Numeral.Stored` was not merely *a* fix but the whole of one. -/

/-- §1: `decimal`'s `ker p` is equality — its `p` is the identity on the digits. -/
theorem ker_decimalCodec {x y : WFNumeral} (h : decimalCodec.Ker (.n x) (.n y))
    (hx : Numeral.Stored x.1 = true) : x.1 = y.1 := by
  have h' : decimalCodec.p (.n x) = decimalCodec.p (.n y) := h
  rw [decimalCodec_p_n, decimalCodec_p_n, if_pos hx] at h'
  by_cases hy : Numeral.Stored y.1 = true
  · rw [if_pos hy] at h'
    exact Value.str.inj (Option.some.inj h')
  · rw [if_neg hy] at h'; exact nomatch h'

/-- §1: `Can(decimal)` is the normal forms and a normalisation fixes its own, so `Stored`
    discharges `η ⊆ ker p`. Necessity is `not_survivesStore_wfDecimalCodec`. -/
theorem survivesStore_decimalCodec {η : Attr → Attr}
    (hη : ∀ s : WFNumeral, Numeral.Stored s.1 = true → η (.n s) = .n s) :
    SurvivesStore decimalCodec η := by
  rintro a ⟨v, hv⟩
  cases v with
  | str s =>
    rw [decimalCodec_e_str] at hv
    by_cases hs : Numeral.Stored s = true
    · rw [dif_pos hs] at hv
      cases hv
      show decimalCodec.p (η (.n ⟨s, _⟩)) = decimalCodec.p (.n ⟨s, _⟩)
      rw [hη ⟨s, Numeral.stored_wf hs⟩ hs]
    · rw [dif_neg hs] at hv; exact nomatch hv
  | _ => exact nomatch hv

/-- The `(number)` case — the one consuming the shortest-text axiom. -/
theorem lawful_numberCodec : Lawful numberCodec := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t a he
    cases t with
    | num d =>
      rw [numberCodec_e_num] at he
      by_cases hw : Numeral.WF d.toDec = true
      · rw [dif_pos hw] at he; cases he
        rw [numberCodec_p_n]
        show ((Double.ofDec (⟨d.toDec, hw⟩ : WFNumeral).1).bind
          (fun e => if Numeral.WF e.toDec then some (Value.num e) else none)) = some (.num d)
        rw [Double.roundtrip, Option.some_bind, if_pos hw]
      · rw [dif_neg hw] at he; exact nomatch he
    | _ => exact nomatch he
  · intro a t hp
    cases a with
    | n x =>
      rw [numberCodec_p_n] at hp
      cases hx : Double.ofDec x.1 with
      | none => rw [hx] at hp; exact nomatch hp
      | some d =>
        rw [hx] at hp
        replace hp : (if Numeral.WF d.toDec then some (Value.num d) else none) = some t := hp
        by_cases hw : Numeral.WF d.toDec = true
        · rw [if_pos hw] at hp; cases hp
          rw [numberCodec_e_num, dif_pos hw]; rfl
        · rw [if_neg hw] at hp; exact nomatch hp
    | _ => exact nomatch hp
  · intro μ hμ t a he
    cases t with
    | num d =>
      rw [numberCodec_e_num] at he
      by_cases hw : Numeral.WF d.toDec = true
      · rw [dif_pos hw] at he; cases he; cases hμ; rfl
      · rw [dif_neg hw] at he; exact nomatch he
    | _ => exact nomatch he
  · intro a t a' hp he
    cases a with
    | n x =>
      rw [numberCodec_p_n] at hp
      cases hx : Double.ofDec x.1 with
      | none => rw [hx] at hp; exact nomatch hp
      | some d =>
        rw [hx] at hp
        replace hp : (if Numeral.WF d.toDec then some (Value.num d) else none) = some t := hp
        by_cases hw : Numeral.WF d.toDec = true
        · rw [if_pos hw] at hp; cases hp
          rw [numberCodec_e_num, dif_pos hw] at he
          cases he
          exact .n ..
        · rw [if_neg hw] at hp; exact nomatch hp
    | _ => exact nomatch hp

theorem LawfulCore.through {c : Codec} (h : LawfulCore c) {f g : Value → Value}
    (hiso : IsoCancels c f g) :
    LawfulCore (c.through f g) where
  retract he := through_p.mpr ⟨_, h.retract (through_e.mp he),
    (hiso.1 _ (by rw [through_e.mp he]; rfl)).symm⟩
  canon hp := by
    obtain ⟨w, hw, rfl⟩ := through_p.mp hp
    show (c.e (f (g w))).isSome
    rw [hiso.2 w (h.canon hw)]
    exact h.canon hw
  writes := by intro μ hμ t a he; exact h.writes hμ (through_e.mp he)

/-- `held` preserves the full laws: the core lemma, plus `≼` through the iso. -/
theorem Lawful.through {c : Codec} (h : Lawful c) {f g : Value → Value}
    (hiso : IsoCancels c f g) :
    Lawful (c.through f g) :=
  { LawfulCore.through h.core hiso with
    agree := by
      intro a t a' hp he
      obtain ⟨w, hw, rfl⟩ := through_p.mp hp
      rw [through_e, hiso.2 w (h.canon hw)] at he
      exact h.agree hw he }

/-- `refine` preserves the laws: everything restricts. -/
theorem LawfulCore.restrict {c : Codec} (h : LawfulCore c) (q : Value → Bool) :
    LawfulCore (c.restrict q) where
  retract he :=
    let ⟨hq, hc⟩ := restrict_e.mp he
    restrict_p.mpr ⟨h.retract hc, hq⟩
  canon hp :=
    let ⟨hc, hq⟩ := restrict_p.mp hp
    Option.isSome_iff_exists.mpr
      (let ⟨a, ha⟩ := Option.isSome_iff_exists.mp (h.canon hc)
       ⟨a, restrict_e.mpr ⟨hq, ha⟩⟩)
  writes := by intro μ hμ t a he; exact h.writes hμ (restrict_e.mp he).2

theorem Lawful.restrict {c : Codec} (h : Lawful c) (q : Value → Bool) :
    Lawful (c.restrict q) :=
  { LawfulCore.restrict h.core q with
    agree := fun hp he => h.agree (restrict_p.mp hp).1 (restrict_e.mp he).2 }


/-- …and every base is lawful. -/
theorem lawful_baseCodec : ∀ k : GroundKind, Lawful (baseCodec k)
  | .string  => lawful_stringCodec
  | .number  => lawful_numberCodec
  | .decimal => lawful_decimalCodec
  | .boolean => lawful_booleanCodec
  | .binary  => lawful_binaryCodec
  | .null    => lawful_nullCodec

/-- …and so is each set base's element pair. `decimal` is the one that is not a
    `GroundKind`, which is why this is a second table rather than a composition. -/
theorem lawful_setBase : ∀ b : SetBase, Lawful b.elem
  | .string  => lawful_stringCodec
  | .number  => lawful_numberCodec
  | .decimal => lawful_decimalCodec
  | .binary  => lawful_binaryCodec

/-! ### The literal codec is lawful because its base is

`literal` adds a prism and nothing else, so all four laws come from `Lawful.restrict` — one
statement, because there is one codec. -/

/-- §3 `(literal)` is lawful, full stop.

    **No `ℓ ⊆ D` hypothesis, and the proof never needed one.** `Lawful` relates `e` and `p` to
    each other and never mentions `T`, so a restriction of a lawful pair is lawful whether or
    not the restriction is inhabited. That is why §3's `ℓ ⊆ D` belongs to the carrier and not
    here. -/
theorem lawful_literalCodec (k : GroundKind) (ls : NEFinset k.Carrier) :
    Lawful (literalCodec k ls) :=
  Lawful.congr (d := (baseCodec k).restrict (inL k ls)) rfl rfl rfl
    (Lawful.restrict (lawful_baseCodec k) (inL k ls))

theorem LawfulCore.extendRead {c : Codec} (h : LawfulCore c) {r : Attr → Option Value}
    (hran : ∀ a v, r a = some v → (c.e v).isSome) :
    LawfulCore (c.extendRead r) where
  retract he := extendRead_p.mpr (.inl (h.retract (extendRead_e.mp he)))
  canon hp := (extendRead_p.mp hp).elim h.canon fun ⟨_, hr⟩ => hran _ _ hr
  writes := by intro μ hμ t a he; exact h.writes hμ (extendRead_e.mp he)

/-- `nullable` keeps the core laws under null-honesty. Structurally this is the sum
    `alt [c, null-point]`; the honesty premises are its (U), specialised — and they are
    used in exactly one place each, to rule out the wrapper's own point colliding with
    the base's. -/
theorem LawfulCore.orNull {c : Codec} (h : LawfulCore c) (hn : NullHonest c) :
    LawfulCore c.orNull where
  retract he := by
    rcases orNull_e.mp he with ⟨rfl, rfl⟩ | ⟨hv, hc⟩
    · exact orNull_p.mpr (.inl ⟨rfl, rfl⟩)
    · exact orNull_p.mpr (.inr ⟨fun hz => hv (hn.1 _ _ hc hz), h.retract hc⟩)
  canon hp := by
    rcases orNull_p.mp hp with ⟨rfl, rfl⟩ | ⟨ha, hc⟩
    · exact Option.isSome_iff_exists.mpr ⟨.null, orNull_e.mpr (.inl ⟨rfl, rfl⟩)⟩
    · obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (h.canon hc)
      exact Option.isSome_iff_exists.mpr
        ⟨a', orNull_e.mpr (.inr ⟨fun hz => ha (hn.2 _ _ hc hz), ha'⟩)⟩
  writes := by intro μ hμ; exact nomatch hμ

/-- `nullable` preserves the full laws: the core lemma, plus `≼` — read-honesty is
    what keeps a non-`NULL` attribute from re-encoding as `⟨NULL, ∗⟩`. -/
theorem Lawful.orNull {c : Codec} (h : Lawful c) (hn : NullHonest c) :
    Lawful c.orNull :=
  { LawfulCore.orNull h.core hn with
    agree := by
      intro a t a' hp he
      rcases orNull_p.mp hp with ⟨rfl, rfl⟩ | ⟨ha, hc⟩
      · rcases orNull_e.mp he with ⟨-, rfl⟩ | ⟨hv, -⟩
        · exact .null
        · exact absurd rfl hv
      · rcases orNull_e.mp he with ⟨rfl, -⟩ | ⟨-, hc'⟩
        · exact absurd (hn.2 _ _ hc rfl) ha
        · exact h.agree hc hc' }

/-! ### `nullable`, as the sugar it is

§3 gives `nullable(c)` a dichotomy: where `c` does not touch the null point it *is*
`union(c, ⟨NULL⟩-point)`, and where `c` does touch it the wrapper adds nothing at all.
`withNull` makes that the *definition* — add the point unless it is already there — and
the two honesty premises stop being premises. They were doing (U)'s job for a
two-option sum by hand; the guard lets lawfulness do it instead. -/

/-- Where `c` does not own the null point, neither half can reach it. -/
theorem ownsNull_false {c : Codec} (hn : c.ownsNull = false) :
    c.e .null = none ∧ c.p .null = none := by
  simp only [Codec.ownsNull, Bool.or_eq_false_iff] at hn
  constructor
  · cases h : c.e .null with
    | none => rfl
    | some _ => rw [h] at hn; exact nomatch hn.1
  · cases h : c.p .null with
    | none => rfl
    | some _ => rw [h] at hn; exact nomatch hn.2

/-- **§3's null-honesty is a consequence, not a premise.** Under the guard, a lawful `c`
    cannot write `⟨NULL, ∗⟩` — (R) would make it read the point straight back — and
    cannot read to `null` — (C) would make it write the point. Both hypotheses are
    refuted rather than assumed. -/
theorem nullHonest_of_not_ownsNull {c : Codec} (h : LawfulCore c)
    (hn : c.ownsNull = false) : NullHonest c := by
  obtain ⟨he, hp⟩ := ownsNull_false hn
  refine ⟨fun v a hv hz => ?_, fun a v hv hz => ?_⟩
  · subst hz; rw [h.retract hv] at hp; exact nomatch hp
  · subst hz
    have hc := h.canon hv
    rw [he] at hc; exact nomatch hc

/-- §3 `(nullable)`: add the null point unless `c` already owns it. `T` and `μ` do not
    depend on the guard — the rule concludes `T + 𝟙 ⇝ ⊤` either way; only the pair moves. -/
def Codec.withNull (c : Codec) : Codec :=
  { T := fun v => c.T v ∨ v = .null
    μ := none
    e := if c.ownsNull then c.e else addPoint (· matches .null) .null c.e
    p := if c.ownsNull then c.p else addPoint (· matches .null) .null c.p }

/-- Where `c` does not own the point, the wrapper *is* `orNull` — §3's first branch. -/
theorem withNull_eq_orNull {c : Codec} (h : c.ownsNull = false) : c.withNull = c.orNull := by
  simp only [Codec.withNull, Codec.orNull, h, if_false, Bool.false_eq_true]

/-- …and where it does, the wrapper adds nothing to the pair — §3's second branch,
    `orNull_eq_self` made definitional. -/
theorem withNull_e_of_owns {c : Codec} (h : c.ownsNull = true) : c.withNull.e = c.e := by
  simp only [Codec.withNull, h, if_true]

theorem withNull_p_of_owns {c : Codec} (h : c.ownsNull = true) : c.withNull.p = c.p := by
  simp only [Codec.withNull, h, if_true]

/-- §3 `(nullable)` keeps the core laws, with **no** honesty premise. -/
theorem lawfulCore_withNull {c : Codec} (h : LawfulCore c) :
    LawfulCore c.withNull := by
  cases hw : c.ownsNull with
  | false => exact withNull_eq_orNull hw ▸ h.orNull (nullHonest_of_not_ownsNull h hw)
  | true =>
    exact { retract := fun he => by
              rw [withNull_p_of_owns hw]; rw [withNull_e_of_owns hw] at he; exact h.retract he
            canon := fun hp => by
              rw [withNull_e_of_owns hw]; rw [withNull_p_of_owns hw] at hp; exact h.canon hp
            writes := fun hμ => nomatch hμ }

/-- …and the full laws, likewise premise-free. -/
theorem lawful_withNull {c : Codec} (h : Lawful c) : Lawful c.withNull := by
  cases hw : c.ownsNull with
  | false =>
    exact withNull_eq_orNull hw ▸ h.orNull (nullHonest_of_not_ownsNull h.core hw)
  | true =>
    exact { lawfulCore_withNull h.core with
            agree := fun hp he => by
              rw [withNull_p_of_owns hw] at hp; rw [withNull_e_of_owns hw] at he
              exact h.agree hp he }

/-- The carrier survives the guard: the held set gains the null point in both branches. -/
theorem carrier_withNull {c : Codec} (h : Carrier c) : Carrier c.withNull := by
  cases hw : c.ownsNull with
  | false => exact withNull_eq_orNull hw ▸ carrier_orNull h
  | true =>
    exact { domE := fun he => by rw [withNull_e_of_owns hw] at he; exact Or.inl (h.domE he)
            ranP := fun hp => by rw [withNull_p_of_owns hw] at hp; exact Or.inl (h.ranP hp) }

/-- §6's idempotence row, **by construction**: the wrapper's own point makes the second
    insertion find it present, so the pair is untouched. It needed null-honesty to be
    lawful; now it needs nothing. -/
theorem withNull_ownsNull {c : Codec} : c.withNull.ownsNull = true := by
  cases hw : c.ownsNull with
  | false =>
    have he : c.withNull.e .null = some .null := by simp [Codec.withNull, addPoint, hw]
    simp [Codec.ownsNull, he]
  | true =>
    rw [Codec.ownsNull, withNull_e_of_owns hw, withNull_p_of_owns hw]
    exact hw

theorem withNull_idem_e {c : Codec} : c.withNull.withNull.e = c.withNull.e :=
  withNull_e_of_owns withNull_ownsNull

theorem withNull_idem_p {c : Codec} : c.withNull.withNull.p = c.withNull.p :=
  withNull_p_of_owns withNull_ownsNull

/-! ## Lawfulness — the open frontier (README roadmap) -/

/-! ### `setCodec`'s laws

Every one of these was a traversal argument over a list; on `Finset` they are the element
codec's own laws lifted by `setImage_inv`. What used to need ~~asWireSet~~'s three-way
payload split and a non-emptiness side condition needs neither: the split is the three
constructors, and non-emptiness is `Finset.Nonempty`. -/

/-- The three wire prisms invert as `setImage_roundTrip` wants. -/
theorem sC_out_inj (a : Attr) (b : String) (h : sC.out a = some b) : a = .s b := by
  cases a <;> simp_all [sC]
theorem nC_out_inj (a : Attr) (b : WFNumeral) (h : nC.out a = some b) : a = .n b := by
  cases a <;> simp_all [nC]
theorem bC_out_inj (a : Attr) (b : Bytes) (h : bC.out a = some b) : a = .b b := by
  cases a <;> simp_all [bC]

/-- A payload projection pins the member. -/
theorem member_of_sC {a : Attr} (h : (sC.out a).isSome = true) : a.member = .S := by
  cases a <;> simp_all [sC, Attr.member]
theorem member_of_nC {a : Attr} (h : (nC.out a).isSome = true) : a.member = .N := by
  cases a <;> simp_all [nC, Attr.member]
theorem member_of_bC {a : Attr} (h : (bC.out a).isSome = true) : a.member = .B := by
  cases a <;> simp_all [bC, Attr.member]


/-- What each wire element reads back to: the value it came from. -/
theorem setImage_read {α β : Type} [DecidableEq β] {c : Codec} (h : LawfulCore c)
    {vinj : α → Value} {aout : Attr → Option β} {ainj : β → Attr}
    (hA : ∀ a b, aout a = some b → a = ainj b)
    {S : Finset α} {T : Finset β}
    (hI : setImage (fun x => (c.e (vinj x)).bind aout) S = some T) :
    ∀ y ∈ T, ∃ x ∈ S, c.p (ainj y) = some (vinj x) := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := (mem_setImage hI y).mp hy
  simp only [Option.bind_eq_some] at hxy
  obtain ⟨a, hea, hoa⟩ := hxy
  rw [hA a y hoa] at hea
  exact ⟨x, hx, h.retract hea⟩

/-- `decSet` lands on the string branch when the reads produce strings. -/
theorem decSet_strBranch {α : Type} {c : Codec} {inj : α → Attr} {S : NEFinset α}
    {U : NEFinset String}
    (h1 : neSetImage (fun y => (c.p (inj y)).bind vStr) S = some U) :
    decSet c inj S = some (.strSet U) := by
  unfold decSet; rw [h1]

/-- …the numeric branch when they produce numbers, the string branch having failed. -/
theorem decSet_numBranch {α : Type} {c : Codec} {inj : α → Attr} {S : NEFinset α}
    {U : NEFinset Double}
    (h0 : neSetImage (fun y => (c.p (inj y)).bind vStr) S = none)
    (h1 : neSetImage (fun y => (c.p (inj y)).bind vNum) S = some U) :
    decSet c inj S = some (.numSet U) := by
  unfold decSet; rw [h0, h1]

/-- …and the binary branch when both earlier ones have. -/
theorem decSet_binBranch {α : Type} {c : Codec} {inj : α → Attr} {S : NEFinset α}
    {U : NEFinset Bytes}
    (h0 : neSetImage (fun y => (c.p (inj y)).bind vStr) S = none)
    (h0' : neSetImage (fun y => (c.p (inj y)).bind vNum) S = none)
    (h1 : neSetImage (fun y => (c.p (inj y)).bind vBin) S = some U) :
    decSet c inj S = some (.binSet U) := by
  unfold decSet; rw [h0, h0', h1]; rfl

/-- **(R) for `set`.** The wire image inverts by `setImage_inv`, and the read side lands on
    the branch the element codec's own reads determine — the *value* kind fixes it, whichever
    wire member the write happened to use. -/
theorem set_retract {c : Codec} (h : LawfulCore c) :
    ∀ {t a}, (setCodec c).e t = some a → (setCodec c).p a = some t := by
  -- Both helpers lose a `Nonempty` argument: `℘⁺fin` carries it, so `key` returns only
  -- the round trip and `miss` takes its witness from `T.2`.
  have key : ∀ {α β : Type} [DecidableEq α] [DecidableEq β]
      {vinj : α → Value} {aout : Attr → Option β} {ainj : β → Attr}
      {vout : Value → Option α},
      (∀ a b, aout a = some b → a = ainj b) → (∀ x, vout (vinj x) = some x) →
      ∀ {S : NEFinset α} {T : NEFinset β},
        neSetImage (fun x => (c.e (vinj x)).bind aout) S = some T →
        neSetImage (fun y => (c.p (ainj y)).bind vout) T = some S := by
    intro α β _ _ vinj aout ainj vout hA hV S T hI
    exact neSetImage_eq_setImage.mpr
      (setImage_roundTrip h hA hV (neSetImage_eq_setImage.mp hI))
  have miss : ∀ {α β γ : Type} [DecidableEq β] [DecidableEq γ]
      {vinj : α → Value} {aout : Attr → Option β} {ainj : β → Attr}
      {vout : Value → Option γ},
      (∀ a b, aout a = some b → a = ainj b) → (∀ x, vout (vinj x) = none) →
      ∀ {S : NEFinset α} {T : NEFinset β},
        neSetImage (fun x => (c.e (vinj x)).bind aout) S = some T →
        neSetImage (fun y => (c.p (ainj y)).bind vout) T = none := by
    intro α β γ _ _ vinj aout ainj vout hA hV S T hI
    obtain ⟨y, hy⟩ := T.2
    obtain ⟨x, -, hpx⟩ := setImage_read h hA (neSetImage_eq_setImage.mp hI) y hy
    exact neSetImage_none (setImage_none_of hy (by rw [hpx]; simpa using hV x))
  intro t a he
  rcases setCodec_e_eq.mp he with ⟨S, rfl, hE⟩ | ⟨S, rfl, hE⟩ | ⟨S, rfl, hE⟩ <;>
    (unfold encSet at hE
     split at hE
     · next T hT =>
       injection hE with hE; subst hE
       first
       | exact decSet_strBranch
           (key (vinj := Value.str) (vout := vStr) sC_out_inj (fun _ => rfl) hT)
       | exact decSet_numBranch
           (miss (vinj := Value.num) (vout := vStr) sC_out_inj (fun _ => rfl) hT)
           (key (vinj := Value.num) (vout := vNum) sC_out_inj (fun _ => rfl) hT)
       | exact decSet_binBranch
           (miss (vinj := Value.bin) (vout := vStr) sC_out_inj (fun _ => rfl) hT)
           (miss (vinj := Value.bin) (vout := vNum) sC_out_inj (fun _ => rfl) hT)
           (key (vinj := Value.bin) (vout := vBin) sC_out_inj (fun _ => rfl) hT)
     · split at hE
       · next T hT =>
         injection hE with hE; subst hE
         first
         | exact decSet_strBranch
             (key (vinj := Value.str) (vout := vStr) nC_out_inj (fun _ => rfl) hT)
         | exact decSet_numBranch
             (miss (vinj := Value.num) (vout := vStr) nC_out_inj (fun _ => rfl) hT)
             (key (vinj := Value.num) (vout := vNum) nC_out_inj (fun _ => rfl) hT)
         | exact decSet_binBranch
             (miss (vinj := Value.bin) (vout := vStr) nC_out_inj (fun _ => rfl) hT)
             (miss (vinj := Value.bin) (vout := vNum) nC_out_inj (fun _ => rfl) hT)
             (key (vinj := Value.bin) (vout := vBin) nC_out_inj (fun _ => rfl) hT)
       · next =>
         obtain ⟨T, hT, hA⟩ := Option.map_eq_some'.mp hE
         subst hA
         first
         | exact decSet_strBranch
             (key (vinj := Value.str) (vout := vStr) bC_out_inj (fun _ => rfl) hT)
         | exact decSet_numBranch
             (miss (vinj := Value.num) (vout := vStr) bC_out_inj (fun _ => rfl) hT)
             (key (vinj := Value.num) (vout := vNum) bC_out_inj (fun _ => rfl) hT)
         | exact decSet_binBranch
             (miss (vinj := Value.bin) (vout := vStr) bC_out_inj (fun _ => rfl) hT)
             (miss (vinj := Value.bin) (vout := vNum) bC_out_inj (fun _ => rfl) hT)
             (key (vinj := Value.bin) (vout := vBin) bC_out_inj (fun _ => rfl) hT))

/-- **(W) for `set`.** The wire member is `setMember` of the element's, and which branch
    `encSet` took is fixed by the element codec's own member. -/
theorem set_writes {c : Codec} (h : LawfulCore c) :
    ∀ {μ}, (setCodec c).μ = some μ → ∀ {t a}, (setCodec c).e t = some a →
      a.member = μ := by
  intro μ hμ t a he
  replace hμ : c.μ.bind setMember = some μ := hμ
  cases hc : c.μ with
  | none => rw [hc] at hμ; exact nomatch hμ
  | some μ₀ =>
    rw [hc] at hμ
    replace hμ : setMember μ₀ = some μ := hμ
    rcases setCodec_e_eq.mp he with ⟨S, rfl, hE⟩ | ⟨S, rfl, hE⟩ | ⟨S, rfl, hE⟩ <;>
      · obtain ⟨x₀, hx₀⟩ := S.2
        obtain ⟨a₀, ha₀⟩ := Option.isSome_iff_exists.mp (encSet_elem hE x₀ hx₀)
        have hm₀ : a₀.member = μ₀ := h.writes hc ha₀
        unfold encSet at hE
        split at hE
        · next T hT =>
          injection hE with hE; subst hE
          have hs := setImage_some (neSetImage_eq_setImage.mp hT) x₀ hx₀
          rw [ha₀] at hs
          rw [← hm₀, member_of_sC hs] at hμ
          simpa [Attr.member] using Option.some.inj hμ
        · split at hE
          · next T hT =>
            injection hE with hE; subst hE
            have hs := setImage_some (neSetImage_eq_setImage.mp hT) x₀ hx₀
            rw [ha₀] at hs
            rw [← hm₀, member_of_nC hs] at hμ
            simpa [Attr.member] using Option.some.inj hμ
          · next =>
            obtain ⟨T, hT, hA⟩ := Option.map_eq_some'.mp hE
            subst hA
            have hs := setImage_some (neSetImage_eq_setImage.mp hT) x₀ hx₀
            rw [ha₀] at hs
            rw [← hm₀, member_of_bC hs] at hμ
            simpa [Attr.member] using Option.some.inj hμ

/-- Writing a set succeeds when its elements do and the element member is ground: the
    member fixes which branch `encSet` takes, and (R) supplies the injectivity. -/
theorem encSet_isSome_of {α : Type} {c : Codec} (h : LawfulCore c)
    {μ₀ μS : Member} (hsm : setMember μ₀ = some μS)
    {vinj : α → Value} (hvi : ∀ x y, vinj x = vinj y → x = y)
    {S : NEFinset α}
    (hall : ∀ x ∈ S.1, (c.e (vinj x)).isSome = true)
    (hmem : ∀ x ∈ S.1, ∀ a', c.e (vinj x) = some a' → a'.member = μ₀) :
    (encSet c vinj S).isSome = true := by
  obtain ⟨x₀, hx₀⟩ := S.2
  unfold encSet
  -- the element member decides the branch
  cases μ₀
  case S =>
    have hb : ∀ x ∈ S.1, ((c.e (vinj x)).bind sC.out).isSome = true := by
      intro x hx
      obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (hall x hx)
      have := hmem x hx _ ha'
      cases a' <;> simp_all [sC, Attr.member]
    have hinj : ∀ x₁ ∈ S.1, ∀ x₂ ∈ S.1, ∀ y,
        (c.e (vinj x₁)).bind sC.out = some y → (c.e (vinj x₂)).bind sC.out = some y →
        x₁ = x₂ := by
      intro x₁ _ x₂ _ y h1 h2
      simp only [Option.bind_eq_some] at h1 h2
      obtain ⟨a₁, he₁, ho₁⟩ := h1
      obtain ⟨a₂, he₂, ho₂⟩ := h2
      rw [sC_out_inj a₁ y ho₁] at he₁
      rw [sC_out_inj a₂ y ho₂] at he₂
      exact hvi _ _ ((h.retract he₁).symm.trans (h.retract he₂) |> Option.some.inj)
    obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp (setImage_isSome_of hb hinj)
    rw [(neSetImage_eq_setImage (T := ⟨T, setImage_nonempty hT S.2⟩)).mpr hT]; rfl
  case N =>
    have hb : ∀ x ∈ S.1, ((c.e (vinj x)).bind sC.out).isSome = true → False := by
      intro x hx hcon
      obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (hall x hx)
      have := hmem x hx _ ha'
      rw [ha'] at hcon
      cases a' <;> simp_all [sC, Attr.member]
    have hb2 : ∀ x ∈ S.1, ((c.e (vinj x)).bind nC.out).isSome = true := by
      intro x hx
      obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (hall x hx)
      have := hmem x hx _ ha'
      cases a' <;> simp_all [nC, Attr.member]
    have hinj : ∀ x₁ ∈ S.1, ∀ x₂ ∈ S.1, ∀ y,
        (c.e (vinj x₁)).bind nC.out = some y → (c.e (vinj x₂)).bind nC.out = some y →
        x₁ = x₂ := by
      intro x₁ _ x₂ _ y h1 h2
      simp only [Option.bind_eq_some] at h1 h2
      obtain ⟨a₁, he₁, ho₁⟩ := h1
      obtain ⟨a₂, he₂, ho₂⟩ := h2
      rw [nC_out_inj a₁ y ho₁] at he₁
      rw [nC_out_inj a₂ y ho₂] at he₂
      exact hvi _ _ ((h.retract he₁).symm.trans (h.retract he₂) |> Option.some.inj)
    have hfail : setImage (fun x => (c.e (vinj x)).bind sC.out) S = none :=
      setImage_none_of hx₀ (by
        cases hcon : (c.e (vinj x₀)).bind sC.out with
        | none => rfl
        | some _ => exact absurd (by rw [hcon]; rfl) (fun hh => hb x₀ hx₀ hh))
    obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp (setImage_isSome_of hb2 hinj)
    rw [neSetImage_none hfail,
      (neSetImage_eq_setImage (T := ⟨T, setImage_nonempty hT S.2⟩)).mpr hT]; rfl
  case B =>
    have hfailS : setImage (fun x => (c.e (vinj x)).bind sC.out) S = none :=
      setImage_none_of hx₀ (by
        obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (hall x₀ hx₀)
        have := hmem x₀ hx₀ _ ha'
        cases a' <;> simp_all [sC, Attr.member])
    have hfailN : setImage (fun x => (c.e (vinj x)).bind nC.out) S = none :=
      setImage_none_of hx₀ (by
        obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (hall x₀ hx₀)
        have := hmem x₀ hx₀ _ ha'
        cases a' <;> simp_all [nC, Attr.member])
    have hb : ∀ x ∈ S.1, ((c.e (vinj x)).bind bC.out).isSome = true := by
      intro x hx
      obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (hall x hx)
      have := hmem x hx _ ha'
      cases a' <;> simp_all [bC, Attr.member]
    have hinj : ∀ x₁ ∈ S.1, ∀ x₂ ∈ S.1, ∀ y,
        (c.e (vinj x₁)).bind bC.out = some y → (c.e (vinj x₂)).bind bC.out = some y →
        x₁ = x₂ := by
      intro x₁ _ x₂ _ y h1 h2
      simp only [Option.bind_eq_some] at h1 h2
      obtain ⟨a₁, he₁, ho₁⟩ := h1
      obtain ⟨a₂, he₂, ho₂⟩ := h2
      rw [bC_out_inj a₁ y ho₁] at he₁
      rw [bC_out_inj a₂ y ho₂] at he₂
      exact hvi _ _ ((h.retract he₁).symm.trans (h.retract he₂) |> Option.some.inj)
    obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp (setImage_isSome_of hb hinj)
    rw [neSetImage_none hfailS, neSetImage_none hfailN,
      (neSetImage_eq_setImage (T := ⟨T, setImage_nonempty hT S.2⟩)).mpr hT]; rfl
  all_goals exact nomatch hsm


/-- Core set: (R), (C) and (W). The `(set)` rule's member premise is what fixes which wire
    branch the write takes, so it is still a hypothesis — but nothing else is, and in
    particular no traversal and no non-emptiness side condition. -/
theorem lawfulCore_setCodec {c : Codec} {μ₀ μS : Member} (h : LawfulCore c)
    (hμ : c.μ = some μ₀) (hsm : setMember μ₀ = some μS) :
    LawfulCore (setCodec c) := by
  refine ⟨set_retract h, ?_, set_writes h⟩
  intro a t hp
  rcases setCodec_p_eq.mp hp with ⟨S, rfl, hD⟩ | ⟨S, rfl, hD⟩ | ⟨S, rfl, hD⟩ <;>
    · rcases decSet_mem hD with ⟨U, rfl, hm⟩ | ⟨U, rfl, hm⟩ | ⟨U, rfl, hm⟩ <;>
      · refine encSet_isSome_of h hsm (fun x y hxy => by injection hxy) ?_
          (fun x _ a' ha' => h.writes hμ ha')
        intro y hy
        obtain ⟨x, -, hpx⟩ := hm y hy
        exact h.canon hpx


/-! ### Which branch `encSet` takes

`encSet` tries `SS`, then `NS`, then `BS`. `lawfulCore_setCodec` only needed to know that
*some* branch fires; **(A)** needs to know *which*, because `Agree` pairs a wire set with a
wire set of the same family. The member of the elements' attributes decides it. -/

/-- Elements at member `S` take the `SS` branch. -/
theorem encSet_ss_of {α : Type} {c : Codec} {vinj : α → Value} {S : NEFinset α} {a : Attr}
    (hm : ∀ x ∈ S.1, ∀ b, c.e (vinj x) = some b → b.member = .S)
    (h : encSet c vinj S = some a) : ∃ T, a = .ss T := by
  obtain ⟨x₀, hx₀⟩ := S.2
  have hall := encSet_elem h
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hall x₀ hx₀)
  have hbm := hm x₀ hx₀ b hb
  unfold encSet at h
  cases hT : neSetImage (fun x => (c.e (vinj x)).bind sC.out) S with
  | some T => rw [hT] at h; exact ⟨T, (Option.some.inj h).symm⟩
  | none =>
    exfalso
    have hN : neSetImage (fun x => (c.e (vinj x)).bind nC.out) S = none :=
      neSetImage_none (setImage_none_of hx₀ (by cases b <;> simp_all [nC, Attr.member]))
    have hB : neSetImage (fun x => (c.e (vinj x)).bind bC.out) S = none :=
      neSetImage_none (setImage_none_of hx₀ (by cases b <;> simp_all [bC, Attr.member]))
    rw [hT, hN, hB] at h
    simp at h

/-- Elements at member `N` take the `NS` branch, the `SS` one having failed. -/
theorem encSet_ns_of {α : Type} {c : Codec} {vinj : α → Value} {S : NEFinset α} {a : Attr}
    (hm : ∀ x ∈ S.1, ∀ b, c.e (vinj x) = some b → b.member = .N)
    (h : encSet c vinj S = some a) : ∃ T, a = .ns T := by
  obtain ⟨x₀, hx₀⟩ := S.2
  have hall := encSet_elem h
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hall x₀ hx₀)
  have hbm := hm x₀ hx₀ b hb
  have hS : neSetImage (fun x => (c.e (vinj x)).bind sC.out) S = none :=
    neSetImage_none (setImage_none_of hx₀ (by cases b <;> simp_all [sC, Attr.member]))
  unfold encSet at h
  rw [hS] at h
  cases hT : neSetImage (fun x => (c.e (vinj x)).bind nC.out) S with
  | some T => rw [hT] at h; exact ⟨T, (Option.some.inj h).symm⟩
  | none =>
    exfalso
    have hB : neSetImage (fun x => (c.e (vinj x)).bind bC.out) S = none :=
      neSetImage_none (setImage_none_of hx₀ (by cases b <;> simp_all [bC, Attr.member]))
    rw [hT, hB] at h
    simp at h

/-- Elements at member `B` take the `BS` branch, both earlier ones having failed. -/
theorem encSet_bs_of {α : Type} {c : Codec} {vinj : α → Value} {S : NEFinset α} {a : Attr}
    (hm : ∀ x ∈ S.1, ∀ b, c.e (vinj x) = some b → b.member = .B)
    (h : encSet c vinj S = some a) : ∃ T, a = .bs T := by
  obtain ⟨x₀, hx₀⟩ := S.2
  have hall := encSet_elem h
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hall x₀ hx₀)
  have hbm := hm x₀ hx₀ b hb
  have hS : neSetImage (fun x => (c.e (vinj x)).bind sC.out) S = none :=
    neSetImage_none (setImage_none_of hx₀ (by cases b <;> simp_all [sC, Attr.member]))
  have hN : neSetImage (fun x => (c.e (vinj x)).bind nC.out) S = none :=
    neSetImage_none (setImage_none_of hx₀ (by cases b <;> simp_all [nC, Attr.member]))
  unfold encSet at h
  rw [hS, hN] at h
  obtain ⟨T, -, hTa⟩ := Option.map_eq_some'.mp h
  exact ⟨T, hTa.symm⟩


/-- **A set writes exactly when every element does.**

    Both directions, and neither needs a hypothesis the term does not already carry: the
    injectivity `encSet` demands comes from the element pair's own **(R)**
    (`encSet_isSome_of`), and every base's element map is injective for a reason —
    `Double.toDec` from `Double.roundtrip`, the other three by construction. This is why
    indexing `set` makes the value-side row exact where an arbitrary element term could not
    (a `held` adapter may collapse two elements). -/
theorem encSet_base_iff {α : Type} (b : SetBase) {vinj : α → Value}
    (hvi : ∀ x y, vinj x = vinj y → x = y) (S : NEFinset α) :
    (encSet b.elem vinj S).isSome = true ↔ ∀ x ∈ S.1, b.adm (vinj x) = true := by
  constructor
  · intro h x hx
    cases he : encSet b.elem vinj S with
    | none => rw [he] at h; exact nomatch h
    | some a => exact (b.adm_iff (vinj x)).mpr (encSet_elem he x hx)
  · intro h
    exact encSet_isSome_of (lawful_setBase b).core (b.setMember_elemMember) hvi
      (fun x hx => (b.adm_iff (vinj x)).mp (h x hx))
      (fun _ _ a' ha' => (lawful_setBase b).core.writes b.elem_μ ha')

/-- **`setCodec` is lawful**, and the argument is not `lawfulCore_setCodec` with `agree`
    bolted on. That theorem gets member uniformity from `c.μ`, and the two call sites in
    the `opaque` fixpoint cannot supply it: `opaqCodec`'s `μ` is `none`. Here it comes from
    **(A)** instead — a value read out of `Attr.s x` writes back to something that *agrees*
    with `Attr.s x`, hence shares its member — which is a fact about the attribute the read
    came from, not about the codec's index. -/
theorem lawful_setCodec {c : Codec} (h : Lawful c) : Lawful (setCodec c) := by
  refine ⟨set_retract h.core, ?_, set_writes h.core, ?_⟩
  · intro a t hp
    rcases setCodec_p_eq.mp hp with ⟨S, rfl, hD⟩ | ⟨S, rfl, hD⟩ | ⟨S, rfl, hD⟩
    · rcases decSet_mem hD with ⟨U, rfl, hm⟩ | ⟨U, rfl, hm⟩ | ⟨U, rfl, hm⟩ <;>
      · refine encSet_isSome_of (μ₀ := .S) (μS := .SS) h.core rfl
          (fun x y hxy => by injection hxy) ?_ ?_
        · intro y hy
          obtain ⟨x, -, hpx⟩ := hm y hy
          exact h.canon hpx
        · intro y hy a' ha'
          obtain ⟨x, -, hpx⟩ := hm y hy
          exact (h.agree hpx ha').member_eq
    · rcases decSet_mem hD with ⟨U, rfl, hm⟩ | ⟨U, rfl, hm⟩ | ⟨U, rfl, hm⟩ <;>
      · refine encSet_isSome_of (μ₀ := .N) (μS := .NS) h.core rfl
          (fun x y hxy => by injection hxy) ?_ ?_
        · intro y hy
          obtain ⟨x, -, hpx⟩ := hm y hy
          exact h.canon hpx
        · intro y hy a' ha'
          obtain ⟨x, -, hpx⟩ := hm y hy
          exact (h.agree hpx ha').member_eq
    · rcases decSet_mem hD with ⟨U, rfl, hm⟩ | ⟨U, rfl, hm⟩ | ⟨U, rfl, hm⟩ <;>
      · refine encSet_isSome_of (μ₀ := .B) (μS := .BS) h.core rfl
          (fun x y hxy => by injection hxy) ?_ ?_
        · intro y hy
          obtain ⟨x, -, hpx⟩ := hm y hy
          exact h.canon hpx
        · intro y hy a' ha'
          obtain ⟨x, -, hpx⟩ := hm y hy
          exact (h.agree hpx ha').member_eq
  · intro a t a' hp he
    rcases setCodec_p_eq.mp hp with ⟨S, rfl, hD⟩ | ⟨S, rfl, hD⟩ | ⟨S, rfl, hD⟩
    · rcases decSet_mem hD with ⟨U, rfl, hm⟩ | ⟨U, rfl, hm⟩ | ⟨U, rfl, hm⟩ <;>
      · obtain ⟨T, rfl⟩ := encSet_ss_of (fun y hy b hb => by
          obtain ⟨x, -, hpx⟩ := hm y hy
          exact (h.agree hpx hb).member_eq) he
        exact Agree.ss T S
    · rcases decSet_mem hD with ⟨U, rfl, hm⟩ | ⟨U, rfl, hm⟩ | ⟨U, rfl, hm⟩ <;>
      · obtain ⟨T, rfl⟩ := encSet_ns_of (fun y hy b hb => by
          obtain ⟨x, -, hpx⟩ := hm y hy
          exact (h.agree hpx hb).member_eq) he
        exact Agree.ns T S
    · rcases decSet_mem hD with ⟨U, rfl, hm⟩ | ⟨U, rfl, hm⟩ | ⟨U, rfl, hm⟩ <;>
      · obtain ⟨T, rfl⟩ := encSet_bs_of (fun y hy b hb => by
          obtain ⟨x, -, hpx⟩ := hm y hy
          exact (h.agree hpx hb).member_eq) he
        exact Agree.bs T S


/-! ### Keyed lookup and traversal facts (the keyed product consumes these) -/


/-- **What `fbNames` contains**: exactly the `fb` names the row omits.

    The list form needed a forty-line induction over the row; a `Finset.filter` needs
    `Finset.mem_filter`, and the four facts the object proofs use still fall out of it. -/
private theorem isFbB_eq {o : Option FieldSem} :
    isFbB o = true ↔ ∃ c v, o = some (.fb c v) := by
  cases o with
  | none => simp [isFbB]
  | some fs => cases fs <;> simp [isFbB]

theorem mem_fbNames {names : Finset Name} {sems : MapOf FieldSem} {k} :
    k ∈ fbNames names sems ↔ (∃ c v, sems.at k = some (.fb c v)) ∧ k ∉ names := by
  simp only [fbNames, Finset.mem_filter, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, isFbB_eq]
  exact ⟨fun ⟨_, hfb, hn⟩ => ⟨hfb, hn⟩,
         fun ⟨⟨c, v, hm⟩, hn⟩ => ⟨(MapOf.at_eq_some.mp hm).1, ⟨c, v, hm⟩, hn⟩⟩

theorem fbNames_mem {sems : MapOf FieldSem} {names : Finset Name} {k c v}
    (hm : sems.at k = some (.fb c v)) (hc : k ∉ names) : k ∈ fbNames names sems :=
  mem_fbNames.mpr ⟨⟨c, v, hm⟩, hc⟩

/-- Emptiness by `Finset.ext`, not by `Finset.eq_empty_of_forall_not_mem`: the mathlib
    lemma is proved classically, and this file's axiom base (`Axioms.lean`) does not
    admit `Classical.choice`. -/
theorem fbNames_empty {sems : MapOf FieldSem} {names : Finset Name}
    (h : ∀ k c v, sems.at k = some (.fb c v) → k ∈ names) : fbNames names sems = ∅ :=
  Finset.ext fun k =>
    ⟨fun hk => by obtain ⟨⟨c, v, hm⟩, hn⟩ := mem_fbNames.mp hk; exact absurd (h k c v hm) hn,
     fun hk => absurd hk (Finset.not_mem_empty k)⟩

/-- The guard characterizations. One `decide` over the key set replaces the `List.all`,
    and the `Nodup` premise that used to accompany every use of them is gone. -/
theorem valPresentB_spec {sems : MapOf FieldSem} {names : Finset Name}
    (h : valPresentB sems names = true) {k fs} (hm : sems.at k = some fs)
    (hno : ∀ c, fs ≠ FieldSem.opt c) : k ∈ names := by
  obtain ⟨hk, rfl⟩ := MapOf.at_eq_some.mp hm
  have hb := of_decide_eq_true h ⟨k, hk⟩
  cases hs : sems.2 ⟨k, hk⟩ with
  | opt c => rw [hs] at hno; exact absurd rfl (hno c)
  | req c => rw [hs] at hb; exact of_decide_eq_true hb
  | fb c v => rw [hs] at hb; exact of_decide_eq_true hb

theorem valPresentB_of {sems : MapOf FieldSem} {names : Finset Name}
    (h : ∀ k fs, sems.at k = some fs → (∀ c, fs ≠ FieldSem.opt c) → k ∈ names) :
    valPresentB sems names = true := by
  refine decide_eq_true fun k => ?_
  cases hs : sems.2 k with
  | opt c => simp [valPresentAt, hs]
  | req c =>
    simpa [valPresentAt, hs] using
      h k.1 (.req c) (by rw [MapOf.at_of_mem k, hs]) (fun _ h' => nomatch h')
  | fb c v =>
    simpa [valPresentAt, hs] using
      h k.1 (.fb c v) (by rw [MapOf.at_of_mem k, hs]) (fun _ h' => nomatch h')

theorem reqPresentB_spec {sems : MapOf FieldSem} {names : Finset Name}
    (h : reqPresentB sems names = true) {k c} (hm : sems.at k = some (.req c)) :
    k ∈ names := by
  obtain ⟨hk, hs⟩ := MapOf.at_eq_some.mp hm
  have hb := of_decide_eq_true h ⟨k, hk⟩
  rw [hs] at hb
  exact of_decide_eq_true hb

theorem reqPresentB_of {sems : MapOf FieldSem} {names : Finset Name}
    (h : ∀ k c, sems.at k = some (.req c) → k ∈ names) :
    reqPresentB sems names = true := by
  refine decide_eq_true fun k => ?_
  cases hs : sems.2 k with
  | req c => simpa [reqPresentAt, hs] using h k.1 c (by rw [MapOf.at_of_mem k, hs])
  | opt c => simp [reqPresentAt, hs]
  | fb c v => simp [reqPresentAt, hs]


/-! ### The keyed steps: round trip, definedness, agreement, and name preservation -/



/-! ### Carriers, continued: objects

    Placed here, after the name-dispatch helpers `p` needs. -/




/-- The same two, stated on the step the payload pair actually takes now: dispatch by
    name, then run that entry's codec. -/
theorem entry_domE' {sems : MapOf FieldSem} {rc? : Option Codec}
    (hs : ∀ k, Carrier (sems.2 k).codec) (hrc : ∀ c ∈ rc?, Carrier c)
    {k : Name} {v : Value} {a : Attr}
    (h : (entryCodec sems rc? k).bind (fun c => c.e v) = some a) :
    objEntryT sems rc? (k, v) := by
  cases hc : entryCodec sems rc? k with
  | none => rw [hc] at h; exact nomatch h
  | some c =>
    rw [hc] at h
    exact objEntryT_eq.mpr ⟨c, hc, (entryCodec_of hs hrc hc).domE h⟩

theorem entry_ranP' {sems : MapOf FieldSem} {rc? : Option Codec}
    (hs : ∀ k, Carrier (sems.2 k).codec) (hrc : ∀ c ∈ rc?, Carrier c)
    {k : Name} {a : Attr} {v : Value}
    (h : (entryCodec sems rc? k).bind (fun c => c.p a) = some v) :
    objEntryT sems rc? (k, v) := by
  cases hc : entryCodec sems rc? k with
  | none => rw [hc] at h; exact nomatch h
  | some c =>
    rw [hc] at h
    exact objEntryT_eq.mpr ⟨c, hc, (entryCodec_of hs hrc hc).ranP h⟩

/-- `fbValue` finds the stand-in a declared `fb` name reads to. -/
theorem fbValue_of {sems : MapOf FieldSem} {k c v}
 (hm : sems.at k = some (.fb c v)) :
    fbValue sems k = some v := by
  simp [fbValue, hm]

/-! #### The rest policy fixes both halves

`objectCodecCore` is stated over a free `rc? : Option Codec` and a free filter
`kn : Name → Bool` because that is what its payload pair takes. Nothing instantiates
them independently: the object rule reads both off one `rest : RestSem`, as `rcOf rest`
and `keepB rest sems`. The three lemmas here are what that costs, discharged once —
they used to be hypotheses on five signatures, and one of them was re-proved by hand at
the call site in `Soundness.lean`. -/

/-- A property of the rest policy's codec, from one per `rest = .codec c`. -/
theorem rcOf_forall {P : Codec → Prop} {rest : RestSem}
    (h : ∀ c, rest = .codec c → P c) : ∀ c ∈ rcOf rest, P c := by
  intro c hc
  cases rest with
  | codec c' =>
    replace hc : some c' = some c := hc
    cases hc
    exact h c rfl
  | drop => exact nomatch hc
  | refuse => exact nomatch hc

/-- What object-encode produces, `keepB` keeps: under `drop` an encoded entry's name
    is declared, and the other policies keep everything. -/
theorem keepB_of_entryWrite {sems : MapOf FieldSem} {rest : RestSem} :
    ∀ k v a, (entryCodec sems (rcOf rest) k).bind (fun c => c.e v) = some a →
      keepB rest sems k = true := by
  intro k v a h
  cases rest with
  | drop =>
    simp only [entryCodec] at h
    cases hsp : sems.at k with
    | none => rw [hsp] at h; simp only [rcOf, Option.bind_none] at h; exact nomatch h
    | some fs => simp [keepB, hsp]
  | refuse => rfl
  | codec rc => rfl

/-- Declared names pass every keep filter. -/
theorem keepB_of_declared {sems : MapOf FieldSem} {rest : RestSem} :
    ∀ k, (sems.at k).isSome = true → keepB rest sems k = true := by
  intro k h
  cases rest with
  | drop => exact h
  | refuse => rfl
  | codec rc => rfl

/-- §4's held set, both ways. The one premise past lawfulness is the doc's own: `hfb` is
    `(fallback)`'s `v(∗) ∈ dom(e)`, which with `domE` gives §4's `v : 𝟙 → T`. That the name
    filter never discards a declared name is not a premise but a fact about the policies —
    `keepB_of_declared`, discharged inline below, and true of all three.

    Writing is immediate. Reading has to account for the stand-ins: every non-`opt`
    name is present in the result — a `req` from the row it was stored in, an `fb`
    from the row or else from its stand-in — and every entry is on its set, the kept
    ones by `entry_ranP'`, the stand-ins by `hfb`. -/
theorem carrier_objectCodec {sems : MapOf FieldSem} {rest : RestSem}
    (hsems : ∀ k, Carrier (sems.2 k).codec)
    (hrc : ∀ rc, rcOf rest = some rc → Carrier rc)
    (hfb : ∀ k c v, sems.2 k = .fb c v → (c.e v).isSome) :
    Carrier (objectCodec sems rest) := by
  show Carrier (objectCodecCore sems (rcOf rest) (keepB rest sems))
  refine objectCodecCore_eq ▸ carrier_carried ?_ ?_
  · rintro p q h
    obtain ⟨hval, g, hg, rfl⟩ := objWrite_eq.mp h
    exact ⟨hval, fun k => entry_domE' hsems hrc (funImage_some hg k)⟩
  · rintro q p h
    obtain ⟨hreq, d, hd, rfl⟩ := objRead_eq.mp h
    constructor
    · refine valPresentB_of fun k fs hm hno => ?_
      have hkn : keepB rest sems k = true := keepB_of_declared k (by rw [hm]; rfl)
      rw [Finset.mem_union]
      cases fs with
      | opt c => exact absurd rfl (hno c)
      | req c =>
        exact Or.inl (Finset.mem_filter.mpr ⟨reqPresentB_spec hreq hm, by simpa using hkn⟩)
      | fb c v₀ =>
        by_cases hk : k ∈ q.1
        · exact Or.inl (Finset.mem_filter.mpr ⟨hk, by simpa using hkn⟩)
        · exact Or.inr (fbNames_mem hm hk)
    · intro k
      by_cases hk : k.1 ∈ q.1.filter (keepB rest sems ·)
      · simp only [dif_pos hk]
        exact entry_ranP' hsems hrc (funImage_some hd ⟨k.1, hk⟩)
      · simp only [dif_neg hk]
        have hfbm : k.1 ∈ fbNames q.1 sems :=
          (Finset.mem_union.mp k.2).resolve_left hk
        obtain ⟨⟨c, v₀, hm⟩, -⟩ := mem_fbNames.mp hfbm
        obtain ⟨hk', hs⟩ := MapOf.at_eq_some.mp hm
        rw [fbValue_of hm]
        refine objEntryT_eq.mpr ⟨c, ?_, ?_⟩
        · simp [entryCodec, hm, FieldSem.codec]
        · obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (hfb ⟨k.1, hk'⟩ c v₀ hs)
          exact (MapOf.at_forall (Q := fun fs => Carrier fs.codec) hsems hm).domE ha'





/-! #### §2's clauses for the object's payload pair

Each is proved once, from core children, and both `lawfulCore_objectCodec` and
`lawful_objectCodec` consume them. -/

section ObjectLaws
variable {sems : MapOf FieldSem} {rest : RestSem}

/-- (R): a written row is complete — every declared name present, none filtered out, no
    stand-in owed — so reading it back is the entrywise round trip and nothing else. -/
theorem object_retract (hf : ∀ k, LawfulCore (sems.2 k).codec)
    (hrc : ∀ c ∈ rcOf rest, LawfulCore c) :
    ∀ p q, objWrite sems (rcOf rest) p = some q →
      objRead sems (rcOf rest) (keepB rest sems) q = some p := by
  rintro p q h
  obtain ⟨hval, g, hg, rfl⟩ := objWrite_eq.mp h
  -- every name of a writable map is kept, so the `drop` filter is the identity
  have hfilter : p.1.filter (keepB rest sems ·) = p.1 :=
    Finset.filter_eq_self.mpr fun k hk => by
      simpa using keepB_of_entryWrite k (p.2 ⟨k, hk⟩) _ (funImage_some hg ⟨k, hk⟩)
  -- and no fallback name is missing, so nothing is adjoined
  have hfb0 : fbNames p.1 sems = ∅ :=
    fbNames_empty fun k c v hm => valPresentB_spec hval hm (fun _ h' => nomatch h')
  refine objRead_eq.mpr ⟨reqPresentB_of fun k c hm =>
    valPresentB_spec hval hm (fun _ h' => nomatch h'), ?_⟩
  refine ⟨fun k => p.2 ⟨k.1, (Finset.mem_filter.mp k.2).1⟩, funImage_eq fun k => ?_, ?_⟩
  · have hw := funImage_some hg ⟨k.1, (Finset.mem_filter.mp k.2).1⟩
    cases hc : entryCodec sems (rcOf rest) k.1 with
    | none => rw [hc] at hw; exact nomatch hw
    | some c =>
      simp only [hc, Option.bind_some] at hw ⊢
      exact (entryCodec_of hf hrc hc).retract hw
  · refine MapOf.ext ?_ ?_
    · simp only [hfilter, hfb0, Finset.union_empty]
    · intro k h₁ h₂
      have hk1 : k ∈ p.1.filter (keepB rest sems ·) := by rw [hfilter]; exact h₁
      simp only [dif_pos hk1]

/-- (C): what was read is writable again — the kept entries by (C) one level down, the
    stand-ins by `(fallback)`'s own premise `v(∗) ∈ dom(e)`. -/
theorem object_canon (hf : ∀ k, LawfulCore (sems.2 k).codec)
    (hrc : ∀ c ∈ rcOf rest, LawfulCore c)
    (hfb : ∀ k c v, sems.2 k = .fb c v → (c.e v).isSome = true) :
    ∀ q p, objRead sems (rcOf rest) (keepB rest sems) q = some p →
      (objWrite sems (rcOf rest) p).isSome = true := by
  rintro q p h
  obtain ⟨hreq, d, hd, rfl⟩ := objRead_eq.mp h
  have hval : valPresentB sems (q.1.filter (keepB rest sems ·) ∪ fbNames q.1 sems) = true := by
    refine valPresentB_of fun k fs hm hno => ?_
    have hknk : keepB rest sems k = true := keepB_of_declared k (by rw [hm]; rfl)
    rw [Finset.mem_union]
    by_cases hk : k ∈ q.1
    · exact Or.inl (Finset.mem_filter.mpr ⟨hk, by simpa using hknk⟩)
    · cases fs with
      | opt c => exact absurd rfl (hno c)
      | req c => exact absurd (reqPresentB_spec hreq hm) hk
      | fb c v => exact Or.inr (fbNames_mem hm hk)
  have hstep : ∀ k : {k // k ∈ q.1.filter (keepB rest sems ·) ∪ fbNames q.1 sems},
      ((entryCodec sems (rcOf rest) k.1).bind (fun c => c.e
        (if h : k.1 ∈ q.1.filter (keepB rest sems ·) then d ⟨k.1, h⟩
         else (fbValue sems k.1).getD .null))).isSome = true := by
    intro k
    by_cases hk : k.1 ∈ q.1.filter (keepB rest sems ·)
    · simp only [dif_pos hk]
      have hp := funImage_some hd ⟨k.1, hk⟩
      cases hc : entryCodec sems (rcOf rest) k.1 with
      | none => rw [hc] at hp; exact nomatch hp
      | some c =>
        simp only [hc, Option.bind_some] at hp ⊢
        exact (entryCodec_of hf hrc hc).canon hp
    · simp only [dif_neg hk]
      obtain ⟨⟨c, v₀, hm⟩, -⟩ :=
        mem_fbNames.mp ((Finset.mem_union.mp k.2).resolve_left hk)
      have hc : entryCodec sems (rcOf rest) k.1 = some c := by
        simp [entryCodec, hm, FieldSem.codec]
      obtain ⟨hk', hs⟩ := MapOf.at_eq_some.mp hm
      simp only [fbValue_of hm, hc, Option.bind_some, Option.getD_some]
      exact hfb ⟨k.1, hk'⟩ c v₀ hs
  simp only [objWrite, if_pos hval]
  exact funImage_map_isSome (funImage_isSome hstep) _

theorem object_agree (hf : ∀ k, Lawful (sems.2 k).codec)
    (hrc : ∀ c ∈ rcOf rest, Lawful c) :
    ∀ q p q', objRead sems (rcOf rest) (keepB rest sems) q = some p →
      objWrite sems (rcOf rest) p = some q' → Agree (mA.into q') (mA.into q) := by
  rintro q p q' hD hE
  obtain ⟨hreq, d, hd, rfl⟩ := objRead_eq.mp hD
  obtain ⟨hval, g, hg, rfl⟩ := objWrite_eq.mp hE
  refine Agree.m _ _ _ _ fun k hx hy => ?_
  -- a name the stored item carries cannot be one the row omits, so the `fb` half of the
  -- union is unreachable here and only the kept entries have to agree
  have hkf : k ∈ q.1.filter (keepB rest sems ·) :=
    (Finset.mem_union.mp hx).resolve_right fun h => (mem_fbNames.mp h).2 hy
  have hp := funImage_some hd ⟨k, hkf⟩
  have hw := funImage_some hg ⟨k, hx⟩
  cases hc : entryCodec sems (rcOf rest) k with
  | none => rw [hc] at hp; exact nomatch hp
  | some c =>
    simp only [hc, Option.bind_some] at hp hw
    simp only [dif_pos hkf] at hw
    exact (entryCodec_of hf hrc hc).agree hp hw

end ObjectLaws

/-- The keyed product — the doc's `object`. `hfb` is §4's `v(∗) ∈ dom(e)`. -/
theorem lawful_objectCodec {sems : MapOf FieldSem} {rest : RestSem}
    (hf : ∀ k, Lawful (sems.2 k).codec)
    (hfb : ∀ k c v, sems.2 k = .fb c v → (c.e v).isSome)
    (hrest : ∀ c, rest = .codec c → Lawful c) :
    Lawful (objectCodec sems rest) := by
  show Lawful (objectCodecCore sems (rcOf rest) (keepB rest sems))
  have hf' := fun k => (hf k).core
  have hrc' := fun c hc => ((rcOf_forall hrest) c hc).core
  exact objectCodecCore_eq ▸ lawful_carried (fun _ => rfl)
    (object_retract hf' hrc') (object_canon hf' hrc' hfb)
    (object_agree hf (rcOf_forall hrest))

theorem lawfulCore_objectCodec {sems : MapOf FieldSem} {rest : RestSem}
    (hf : ∀ k, LawfulCore (sems.2 k).codec)
    (hfb : ∀ k c v, sems.2 k = .fb c v → (c.e v).isSome)
    (hrest : ∀ c, rest = .codec c → LawfulCore c) :
    LawfulCore (objectCodec sems rest) := by
  show LawfulCore (objectCodecCore sems (rcOf rest) (keepB rest sems))
  exact objectCodecCore_eq ▸ lawfulCore_carried (fun _ => rfl)
    (object_retract hf (rcOf_forall hrest)) (object_canon hf (rcOf_forall hrest) hfb)

/-- The sum's core laws. (U) is what makes them hold: it says the option that wrote is
    the only one admitting either side of the pair, so the round trip comes back through
    the same option it went out through. -/
theorem lawfulCore_altCodec {os : List OptionSem} {μA : Option Member}
    (h : ∀ o ∈ os, LawfulCore o.c) (hU : UniqueBothWays os)
    (hW : ∀ m, μA = some m → ∀ o ∈ os, ∀ t a, o.c.e t = some a → a.member = m) :
    LawfulCore (altCodec os μA) where
  retract he := by
    obtain ⟨o, hf, hoe⟩ := altCodec_e.mp he
    have ho := (mem_of_filter_eq_singleton hf).1
    exact altCodec_p.mpr ⟨o, hU.1 o ho _ _ hf hoe, (h o ho).retract hoe⟩
  canon hp := by
    obtain ⟨o, hf, hop⟩ := altCodec_p.mp hp
    have ho := (mem_of_filter_eq_singleton hf).1
    obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp ((h o ho).canon hop)
    exact Option.isSome_iff_exists.mpr
      ⟨a', altCodec_e.mpr ⟨o, hU.2 o ho _ _ _ hf hop ha', ha'⟩⟩
  writes := by
    intro μ hμ t a he
    obtain ⟨o, hf, hoe⟩ := altCodec_e.mp he
    exact hW μ hμ o (mem_of_filter_eq_singleton hf).1 t a hoe

/-- …and (MP) with them: the option that read is the option that re-writes, again by
    (U), so `≼` at the union is `≼` at that one option. -/
theorem lawful_altCodec {os : List OptionSem} {μA : Option Member}
    (h : ∀ o ∈ os, Lawful o.c) (hU : UniqueBothWays os)
    (hW : ∀ m, μA = some m → ∀ o ∈ os, ∀ t a, o.c.e t = some a → a.member = m) :
    Lawful (altCodec os μA) :=
  { lawfulCore_altCodec (fun o ho => (h o ho).core) hU hW with
    agree := by
      intro a t a' hp he
      obtain ⟨o, hf, hop⟩ := altCodec_p.mp hp
      have ho := (mem_of_filter_eq_singleton hf).1
      obtain ⟨a'', ha''⟩ := Option.isSome_iff_exists.mp ((h o ho).canon hop)
      have hV := hU.2 o ho _ _ _ hf hop ha''
      obtain ⟨o', hf', hoe⟩ := altCodec_e.mp he
      have hoo : o' = o := by simpa using hf'.symm.trans hV
      subst hoo
      exact (h _ ho).agree hop hoe }


/-! ### (U) by kind, and `opaque`'s fixpoint

    §5's other disjointness discharger, and the one `(opaque)` needs. An option is
    *pinned to a kind* when it admits only values and attributes of that kind — which is
    precisely what §3 means by calling `opaque`'s options "self-identifying". Pin each
    option and keep the kinds distinct, and (U) follows with nothing said about what the
    options contain: `onKind_set` and its two neighbours hold for *any* element codec,
    which is why the fixpoint's unique admission needs nothing from the recursive call. -/

/-- An option pinned to a kind: it admits only values and attributes of that kind. -/
def OptionSem.OnKind (o : OptionSem) (k : Kind) : Prop :=
  (∀ v, o.admitV v = true → v.kind = k) ∧ (∀ a, o.admitA a = true → a.kind = k)

/-- **(U) by disjoint admissibility** — the structure the rest of this section presents.

    Give each option a set of values and a set of attributes it is allowed to admit, and
    keep each family pairwise disjoint: then no input reaches two options, and admission is
    unique. That is the entire separation argument. Kinds, members, tags and admissible
    sets are *ways of building* those two families, not four different conditions — and
    the two families are independent, which is what lets the value side be separated by a
    kind while the attribute side is separated by a member. -/
theorem uniqueAdmission_of_disjoint {os : List OptionSem}
    {SVs : List (Value → Prop)} {SAs : List (Attr → Prop)}
    (hV : List.Forall₂ (fun o S => ∀ v, o.admitV v = true → S v) os SVs)
    (hA : List.Forall₂ (fun o S => ∀ a, o.admitA a = true → S a) os SAs)
    (hdV : List.Pairwise (fun S T => ∀ v, S v → ¬ T v) SVs)
    (hdA : List.Pairwise (fun S T => ∀ a, S a → ¬ T a) SAs)
    (hw : ∀ o ∈ os, ∀ t a, o.c.e t = some a → o.admitV t = true ∧ o.admitA a = true) :
    UniqueAdmission os := fun o ho t a he =>
  ⟨filter_eq_singleton_of_disjoint hA hdA o ho (hw o ho t a he).2,
   filter_eq_singleton_of_disjoint hV hdV o ho (hw o ho t a he).1⟩

theorem uniqueAdmission_of_sharedBase {base : Codec} {cs : List Codec}
    {qs : List (Value → Bool)} (hlaw : LawfulCore base)
    (hz : List.Forall₂ (fun ci q => ci.e = (base.restrict q).e ∧ ci.p = (base.restrict q).p) cs qs)
    (hdisj : List.Pairwise (fun q q' => ∀ v, q v = true → q' v = false) qs) :
    UniqueAdmission (cs.map OptionSem.byAttempt) := by
  refine uniqueAdmission_of_disjoint
    (SVs := qs.map (fun q v => q v = true))
    (SAs := qs.map (fun q a => ∃ v, base.p a = some v ∧ q v = true)) ?_ ?_ ?_ ?_ ?_
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine hz.imp fun ci q h v hv => ?_
    have : ((base.restrict q).e v).isSome = true := h.1 ▸ hv
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp this
    exact (restrict_e.mp hw).1
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine hz.imp fun ci q h a ha => ?_
    have : ((base.restrict q).p a).isSome = true := h.2 ▸ ha
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp this
    obtain ⟨hp, hq⟩ := restrict_p.mp hw
    exact ⟨w, hp, hq⟩
  · rw [List.pairwise_map]
    refine hdisj.imp fun h v hv hv' => ?_
    simp only at hv hv'; rw [h v hv] at hv'; exact nomatch hv'
  · rw [List.pairwise_map]
    refine hdisj.imp fun h a hx hy => ?_
    obtain ⟨v, hv, hqv⟩ := hx
    obtain ⟨v', hv', hqv'⟩ := hy
    rw [hv] at hv'; cases hv'
    rw [h v hqv] at hqv'; exact nomatch hqv'
  · refine forall_mem_map fun ci hci t a he => ?_
    obtain ⟨q, -, hq⟩ := hz.mem_left hci
    have he' : (base.restrict q).e t = some a := hq.1 ▸ he
    obtain ⟨hqt, hb⟩ := restrict_e.mp he'
    refine ⟨?_, ?_⟩
    · show (ci.e t).isSome = true
      rw [hq.1, he']; rfl
    · show (ci.p a).isSome = true
      rw [hq.2, restrict_p.mpr ⟨hlaw.retract hb, hqt⟩]; rfl

/-- An option pinned to a **set of labels**, under a partial projection of each side of
    the pair. `OnKind` is the singleton case at `Value.kind`/`Attr.kind`; `(dunion)`'s
    tag sets are the general one at `tagOfV`/`tagOfA`. -/
def OptionSem.Labelled {L : Type} (πV : Value → Option L) (πA : Attr → Option L)
    (o : OptionSem) (S : L → Prop) : Prop :=
  (∀ v, o.admitV v = true → ∃ l, πV v = some l ∧ S l) ∧
  (∀ a, o.admitA a = true → ∃ l, πA a = some l ∧ S l)

/-- **(U) by projection** — §5's two outright dischargers, once.

    Label each side of the pair by a partial projection of the input, give each option the
    set of labels it answers to, and keep those sets pairwise disjoint: then no input can
    reach two options, because the label it carries is a property of the *input* and lands
    in at most one option's set. `hw` is the only codec-facing premise, and it is what
    ties a canonical pair to its own option's admission.

    Kind-separation (`opaque`'s fixpoint) and tag-separation (`(dunion)`) are this theorem
    at two projections; §5's table reads as four conditions and is one. -/
theorem uniqueAdmission_of_labels {L : Type} {πV : Value → Option L} {πA : Attr → Option L}
    {os : List OptionSem} {Ss : List (L → Prop)}
    (hz : List.Forall₂ (OptionSem.Labelled πV πA) os Ss)
    (hdisj : List.Pairwise (fun S T => ∀ l, S l → ¬ T l) Ss)
    (hw : ∀ o ∈ os, ∀ t a, o.c.e t = some a → o.admitV t = true ∧ o.admitA a = true) :
    UniqueAdmission os := fun o ho t a he =>
  ⟨filter_eq_singleton_of_labels (hz.imp fun _ _ h => h.2) hdisj o ho (hw o ho t a he).2,
   filter_eq_singleton_of_labels (hz.imp fun _ _ h => h.1) hdisj o ho (hw o ho t a he).1⟩
-- `uniqueAdmission_of_labels` is `uniqueAdmission_of_disjoint` with both families pulled
-- back along one projection; sharing the label type `L` is a convenience of the two cases
-- that need it (a tag, a kind), not part of the structure.

/-- **(U) by kind-separation**, `uniqueAdmission_of_labels` at the total projection
    `Value.kind`/`Attr.kind` with one label per option: `Nodup` is disjointness of
    singletons. -/
theorem uniqueAdmission_of_kinds {os : List OptionSem} {ks : List Kind}
    (hz : List.Forall₂ OptionSem.OnKind os ks) (hnd : ks.Nodup)
    (hw : ∀ o ∈ os, ∀ t a, o.c.e t = some a →
      o.admitV t = true ∧ o.admitA a = true) :
    UniqueAdmission os := by
  refine uniqueAdmission_of_labels (πV := fun v => some v.kind) (πA := fun a => some a.kind)
    (Ss := ks.map (fun k l => l = k)) ?_ ?_ hw
  · rw [List.forall₂_map_right_iff]
    exact hz.imp fun _ _ h =>
      ⟨fun v hv => ⟨_, rfl, h.1 v hv⟩, fun a ha => ⟨_, rfl, h.2 a ha⟩⟩
  · rw [List.pairwise_map]
    exact hnd.imp fun hne l hl hl' => hne (hl.symm.trans hl')

/-- A tag option is `Labelled` by its own tag set, definitionally. -/
theorem labelled_byTag {d : Name} {tags : Finset String} {c : Codec} :
    OptionSem.Labelled (tagOfV d) (tagOfA d) (.byTag d tags c) (· ∈ tags) := by
  refine ⟨fun v hv => ?_, fun a ha => ?_⟩
  · obtain ⟨tag, htv, htag⟩ := byTag_admitV.mp hv
    exact ⟨tag, htv, htag⟩
  · obtain ⟨tag, hta, htag⟩ := byTag_admitA.mp ha
    exact ⟨tag, hta, htag⟩

/-- An option that decides by attempting admits what it writes, on both sides — the
    read side by (R), which is the only thing `hw` above ever needs. -/
theorem byAttempt_write {c : Codec} (h : Lawful c) {t a} (he : c.e t = some a) :
    (OptionSem.byAttempt c).admitV t = true ∧ (OptionSem.byAttempt c).admitA a = true :=
  ⟨by simp [OptionSem.byAttempt, he], by simp [OptionSem.byAttempt, h.retract he]⟩

/-- §5's "the one union whose (U) is a theorem", literally: disjoint tags on stamped
    options give unique admission. `hstamp` is what object-encode of a `req literalS`
    discriminator provides — the tag on the attribute side and the same tag on the
    value side, since a literal writes its value verbatim. (An earlier statement split
    this into an encode-side and a decode-side stamp; the proof showed the value side
    of the *canonical pair* is what admission reads, and only the combined form
    supplies it without assuming (R).) -/
theorem uniqueAdmission_byTag {d : Name} {os : List (Finset String × Codec)}
    (hstamp : ∀ o ∈ os, ∀ t a, o.2.e t = some a →
      ∃ tag ∈ o.1, tagOfA d a = some tag ∧ tagOfV d t = some tag)
    (hdisj : List.Pairwise (fun x y => ∀ tag ∈ x.1, tag ∉ y.1) os) :
    UniqueAdmission (os.map fun o => .byTag d o.1 o.2) := by
  refine uniqueAdmission_of_labels (πV := tagOfV d) (πA := tagOfA d)
    (Ss := os.map (fun o l => l ∈ o.1)) ?_ ?_ ?_
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun o _ => labelled_byTag
  · rw [List.pairwise_map]
    exact hdisj.imp fun h l hl => h l hl
  · refine forall_mem_map fun o ho t a he => ?_
    replace he : o.2.e t = some a := he
    obtain ⟨tag, htag, hA, hV⟩ := hstamp o ho t a he
    exact ⟨byTag_admitV.mpr ⟨tag, hV, htag⟩, byTag_admitA.mpr ⟨tag, hA, htag⟩⟩

/-- Every option of a `(dunion)` writes an `M` — the stamp says so, and the stamp is
    all either strength consults. -/
private theorem dunion_writes {d : Name} {os : List (Finset String × Codec)}
    (hstamp : ∀ o ∈ os, ∀ t a, o.2.e t = some a →
      ∃ tag ∈ o.1, tagOfA d a = some tag ∧ tagOfV d t = some tag) :
    ∀ m, some Member.M = some m →
      ∀ o ∈ os.map fun o => OptionSem.byTag d o.1 o.2,
        ∀ t a, o.c.e t = some a → a.member = m := by
  rintro m hm
  cases hm
  refine forall_mem_map fun x hx t a he => ?_
  replace he : x.2.e t = some a := he
  obtain ⟨tag, htag, hA, -⟩ := hstamp x hx t a he
  -- only an `M` carries a tag at all, so the stamp fixes the member
  cases a <;> simp only [tagOfA] at hA <;> first | rfl | exact nomatch hA

/-- `(dunion)` soundness is a corollary: the sum lemma composed with its (U) theorem;
    the member law comes from the stamp itself — a stamped canonical attribute is an
    `M`. -/
theorem lawful_dunionCodec {d : Name} {os : List (Finset String × Codec)}
    (h : ∀ o ∈ os, Lawful o.2)
    (hstamp : ∀ o ∈ os, ∀ t a, o.2.e t = some a →
      ∃ tag ∈ o.1, tagOfA d a = some tag ∧ tagOfV d t = some tag)
    (hdisj : List.Pairwise (fun x y => ∀ tag ∈ x.1, tag ∉ y.1) os) :
    Lawful (dunionCodec d os) :=
  lawful_altCodec (forall_mem_map h)
    (uniqueBothWays_of_uniqueAdmission (uniqueAdmission_byTag hstamp hdisj))
    (dunion_writes hstamp)

/-- Core `(dunion)`: the same corollary, with core options. -/
theorem lawfulCore_dunionCodec {d : Name} {os : List (Finset String × Codec)}
    (h : ∀ o ∈ os, LawfulCore o.2)
    (hstamp : ∀ o ∈ os, ∀ t a, o.2.e t = some a →
      ∃ tag ∈ o.1, tagOfA d a = some tag ∧ tagOfV d t = some tag)
    (hdisj : List.Pairwise (fun x y => ∀ tag ∈ x.1, tag ∉ y.1) os) :
    LawfulCore (dunionCodec d os) :=
  lawfulCore_altCodec (forall_mem_map h)
    (uniqueBothWays_of_uniqueAdmission (uniqueAdmission_byTag hstamp hdisj))
    (dunion_writes hstamp)

/-! ### `opaque`'s options, each pinned to its kind -/

theorem onKind_string : OptionSem.OnKind (.byAttempt stringCodec) .string := by
  constructor <;> intro x hx <;> cases x <;>
    simp_all [OptionSem.byAttempt, stringCodec, Value.kind, Attr.kind]

theorem onKind_boolean : OptionSem.OnKind (.byAttempt booleanCodec) .boolean := by
  constructor <;> intro x hx <;> cases x <;>
    simp_all [OptionSem.byAttempt, booleanCodec, Value.kind, Attr.kind]

theorem onKind_binary : OptionSem.OnKind (.byAttempt binaryCodec) .binary := by
  constructor <;> intro x hx <;> cases x <;>
    simp_all [OptionSem.byAttempt, binaryCodec, Value.kind, Attr.kind]

theorem onKind_null : OptionSem.OnKind (.byAttempt nullCodec) .null := by
  constructor <;> intro x hx <;> cases x <;>
    simp_all [OptionSem.byAttempt, nullCodec, Value.kind, Attr.kind]

/-- The `Numbers` policy: `lossy` offers the number option, `refuse` offers the empty
    one — which admits nothing, so the pinning holds either way. -/
theorem onKind_number (lossy : Bool) :
    OptionSem.OnKind (.byAttempt (if lossy then numberCodec else Codec.empty)) .number := by
  cases lossy <;> constructor <;> intro x hx <;> cases x <;>
    simp_all [OptionSem.byAttempt, numberCodec, Codec.empty, Value.kind, Attr.kind]

/-- A container option is pinned by its own constructor, whatever it contains. This is
    why the fixpoint's (U) needs nothing from the recursive call — and why `opaque` is
    not a special construction. -/
theorem onKind_set (c : Codec) : OptionSem.OnKind (.byAttempt (setCodec c)) .set := by
  constructor <;> intro x hx <;> cases x <;>
    simp_all [OptionSem.byAttempt, setCodec, Value.kind, Attr.kind]

theorem onKind_array (c : Codec) :
    OptionSem.OnKind (.byAttempt (arrayCodec c)) .array := by
  constructor <;> intro x hx <;> cases x <;>
    simp_all [OptionSem.byAttempt, arrayCodec, Value.kind, Attr.kind]

theorem onKind_record (c : Codec) :
    OptionSem.OnKind (.byAttempt (recordCodec c)) .map := by
  refine ⟨fun v hv => ?_, fun a ha => ?_⟩
  · cases v
    case map keys f => rfl
    all_goals
      (simp only [OptionSem.byAttempt, recordCodec] at hv; exact absurd hv (by simp))
  · cases a
    case m keys g => rfl
    all_goals
      (simp only [OptionSem.byAttempt, recordCodec] at ha; exact absurd ha (by simp))

/-- The kinds `opaque`'s options are pinned to, in the order they are offered. -/
def opaqKinds : List Kind :=
  [.string, .boolean, .binary, .null, .number, .set, .array, .map]

/-- "The recursive union of everything self-identifying" (§3), spelled out: the eight
    options and the eight kinds that identify them. -/
theorem opaq_onKinds (fuel : Nat) (lossy : Bool) :
    List.Forall₂ OptionSem.OnKind (opaqOptions lossy (opaqCodec fuel lossy)) opaqKinds :=
  .cons onKind_string (.cons onKind_boolean (.cons onKind_binary (.cons onKind_null
    (.cons (onKind_number lossy) (.cons (onKind_set _) (.cons (onKind_array _)
      (.cons (onKind_record _) .nil)))))))

/-- The `Numbers` option, lawful either way: `numberCodec` when `lossy`, and the empty
    codec — the absence of an option — when `refuse`. -/
theorem lawful_numOption (lossy : Bool) :
    Lawful (if lossy then numberCodec else Codec.empty) := by
  cases lossy
  · exact Lawful.empty
  · exact lawful_numberCodec

/-- Every option of `opaque` is lawful, given the recursive one is. -/
theorem lawful_opaqOptions {fuel : Nat} {lossy : Bool}
    (hop : Lawful (opaqCodec fuel lossy)) :
    ∀ o ∈ opaqOptions lossy (opaqCodec fuel lossy), Lawful o.c := by
  intro o ho
  simp only [opaqOptions, List.mem_cons] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
  exacts [lawful_stringCodec, lawful_booleanCodec, lawful_binaryCodec,
    lawful_nullCodec, lawful_numOption lossy, lawful_setCodec hop, lawful_arrayCodec hop,
    lawful_recordCodec hop, absurd h (by simp)]

/-- **(U) for `opaque`**, the fourth row of §5's discharger table: the eight options are
    pinned to eight distinct kinds, and each admits what it writes, so admission is
    unique on both sides. The only premise is the recursive option's lawfulness, which
    `uAtCan_opaque` (`Discharge.lean`) discharges. -/
theorem uniqueAdmission_opaque (fuel : Nat) (lossy : Bool)
    (hop : Lawful (opaqCodec fuel lossy)) :
    UniqueAdmission (opaqOptions lossy (opaqCodec fuel lossy)) := by
  refine uniqueAdmission_of_kinds (opaq_onKinds fuel lossy) (by decide) ?_
  intro o ho t a he
  simp only [opaqOptions, List.mem_cons] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
  exacts [byAttempt_write lawful_stringCodec he,
    byAttempt_write lawful_booleanCodec he, byAttempt_write lawful_binaryCodec he,
    byAttempt_write lawful_nullCodec he, byAttempt_write (lawful_numOption lossy) he,
    byAttempt_write (lawful_setCodec hop) he,
    byAttempt_write (lawful_arrayCodec hop) he,
    byAttempt_write (lawful_recordCodec hop) he, absurd h (by simp)]

/-- `opaque` closes with no bespoke induction: the sum lemma, its options' lemmas, and
    unique admission computed from the shapes — kinds partition the values, and the same
    kinds partition the attributes. -/
theorem lawful_opaqCodec : ∀ (fuel : Nat) (lossy : Bool), Lawful (opaqCodec fuel lossy)
  | 0, _ => Lawful.empty
  | fuel+1, lossy =>
    -- `μ` is `⊤`: the options name eight different members, so `unanimous` is `none`
    have hop : Lawful (opaqCodec fuel lossy) := lawful_opaqCodec fuel lossy
    lawful_altCodec (lawful_opaqOptions hop)
      (uniqueBothWays_of_uniqueAdmission (uniqueAdmission_opaque fuel lossy hop))
      (fun _ hm => nomatch hm)

end

end Calculus
