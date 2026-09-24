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
* `extendRead` — the agreeing extension of the reading, for `alternate reader`; canonical reads
  are the sanctioned breach and have no lemma, by design.
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

/-- §3 `(number)`. The held set is `D`, §1's numeral domain, and the carrier is `WFNumeral`,
    so `e` and `p` are constructor wrappers with no gate. -/
def numberCodec : Codec :=
  { T := fun v => ∃ x : WFNumeral, v = .num x
    μ := some .N
    -- **No gate on either half.** The carrier is `WFNumeral`, so the proof `Attr.n` demands
    -- arrives with the value and the read hands the same subtype straight back. The `dite`
    -- that used to make the check and throw it away has nothing left to check.
    e := fun v => match v with
      | .num x => some (.n x)
      | _ => none
    p := fun a => match a with
      | .n x => some (.num x)
      | _ => none }

theorem numberCodec_e_num (x : WFNumeral) : numberCodec.e (.num x) = some (.n x) := rfl

theorem numberCodec_p_n (x : WFNumeral) : numberCodec.p (.n x) = some (.num x) := rfl

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
  | .boolean => booleanCodec
  | .binary  => binaryCodec
  | .null    => nullCodec

/-- §3 `(set)`'s element pair, chosen by the base.

    `denote (.set b)` is `setCodec b.elem`, which is why `setCodec`, `encSet`, `decSet` and
    `setImage` are untouched by the re-indexing: the *constructor* changed, the combinator
    did not. Three bases, three wire members. -/
noncomputable def SetBase.elem : SetBase → Codec
  | .string  => stringCodec
  | .number  => numberCodec
  | .binary  => binaryCodec

/-- `literal(ℓ)`'s predicate: the value is the alternative.

    One definition where there were two (~~inLS~~, ~~inLN~~) and three bases with none. Dispatching
    on the index first is what makes the carrier concrete, and so the equality decidable. -/
noncomputable def inL : (k : GroundKind) → k.Carrier → Value → Bool
  | .string,  x, .str s  => decide (s = x)
  -- `number`'s carrier IS the value's, so this row joins the ungated four: the payload is
  -- the alternative and there is no gate left to go through.
  | .number,  x, .num d  => decide (d = x)
  | .boolean, x, .bool b => decide (b = x)
  | .binary,  x, .bin b  => decide (b = x)
  | .null,    _, .null   => true
  | _, _, _ => false

/-! `inL`'s rows at the five bases, as `@[simp]` equations.

Without these a `simp` that needs `inL` at one base unfolds `inL.match_1` — the matcher Lean
derives for the whole ten-row table — and pays for all ten rows at every rewrite. That is what
~~fanOf~~ found behind `AdmA_exact`'s duplication. Each of the five bases gets an equation. -/

/-- `.str` at `string`: the payload *is* the carrier, so this is `rfl`. -/
@[simp] theorem inL_str (x s : String) :
    inL .string x (.str s) = decide (s = x) := rfl

/-- `.num` at `number`: the carrier is the payload now, so this is `rfl` like the three
    ungated bases beside it. It used to need a `dite` on the host's spelling. -/
@[simp] theorem inL_num (x d : WFNumeral) :
    inL .number x (.num d) = decide (d = x) := rfl

/-- `.bool` at `boolean`, on the same terms. -/
@[simp] theorem inL_bool (x b : Bool) :
    inL .boolean x (.bool b) = decide (b = x) := rfl

/-- `.bin` at `binary`, on the same terms. -/
@[simp] theorem inL_bin (x b : Bytes) :
    inL .binary x (.bin b) = decide (b = x) := rfl

/-- `.null` at `null`: `Unit` has one inhabitant, so the row is `true` and not a comparison. -/
@[simp] theorem inL_null (x : Unit) :
    inL .null x .null = true := rfl

/-- §3's `{ℓ}` — the held set, uniform in the base because `toValue` is. Spelled
    `Value → Prop` rather than `Held`, which is `Typing`'s abbreviation and one module down. -/
def HLit (k : GroundKind) (x : k.Carrier) : Value → Prop :=
  fun v => v = k.toValue x


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
    definition would cost every `rfl` over the two wrappers, and that trade is not worth
    taking blind. The pair is what the claim is about, and the
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

    So the gates are not bespoke: each of the two codecs is `refine` over a base. The
    `decimal` gate is a fact of the store, so the DynamoDB port states it on the pair
    (`decimalCodec_e_restrict`, `DynamoDB.lean`). The bases used to be *ungated*, every
    numeral and every string, and cannot be, now that both sides carry §1's `Numerals`. There is one base at `N`
    instead of the two a host carrier forced, and it is §1's own set: `numberCodec`. The ungated
    bases were standing in for sets the carrier should have been. -/

/-- §1's `D`, as a predicate on values. **It asks only that the value is an `N`**: `D` is the
    well-formed numerals and the carrier is exactly those, so the grammar check that used to
    sit here is carried rather than tested. -/
def inD : Value → Bool :=
  fun v => match v with | .num _ => true | _ => false

/-- **`number` writes exactly on §1's `D`** — stated as the `isSome` of the write, without
    the `dite`.

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
  cases v <;> rfl

/-! ### The base at `N` is §1's own set, and there is exactly ONE of them

**`numberCodec` IS the base at `N`.** `Attr.n` carries `Numeral.WF` and so does the value
side now, so `Carries(N)` is §1's `Numerals` on both halves and no wider codec exists to
refine. ~~wfDecimalCodec~~ was the text-side base beside it, gated at `WF` where `numberCodec`
went through a host spelling; the two are one definition now and the second is deleted. The
DynamoDB port refines it at `Stored` (`DynamoDB.lean`), and `Stored` is a real gate rather
than a carried one. -/

/-- §3 `(literal)`. **The pair is a refinement of its base by construction** — the `refine`
    §7 calls "an iso and a prism", with the prism named by `ℓ` and the iso supplied by the
    index.

    **`T` is deliberately *not* the refinement's**: it stays §3's `ℓ`. That used to mean a
    numeric literal outside `D` was *held* and unwritable, which is (B) failing, and it no
    longer can be: `GroundKind.number`'s carrier is the well-formed numerals, so `HLit` holds
    only values `numberCodec` writes. The transcription that used to exhibit (B) failing here
    is retired, because the value carrier is `D` and there is no outside to point at. -/
noncomputable def literalCodec (k : GroundKind) (x : k.Carrier) : Codec :=
  { (baseCodec k).restrict (inL k x) with T := HLit k x }

theorem literalNCodec_p_n (y : WFNumeral) (x : WFNumeral) :
    (literalCodec .number y).p (.n x) =
      (numberCodec.p (.n x)).bind (fun v => if inL .number y v then some v else none) := rfl

/-! ### The gated ground codecs are refinements

`literal` is not a new construction: it is `string` and `number` with a prism laid over
them, which is exactly what §7 means by "an iso and a prism". Naming the predicates makes
that visible, and lets all four of its laws come from `Lawful.restrict` and
`carrier_restrict` instead of four bespoke inductions.

`decimal` is deliberately *not* here. It moves the member (`str` values to an `N`
attribute), so it is not a refinement of `string` and keeps its own proofs. -/

/-- **§3's gate is `refine` over the base, at every base** — and the numeric one is `number`
    itself rather than a separate ungated numeric term, because §1's `Numerals` is the whole of
    `Carries(N)` and there is no wider numeric pair. That is what makes numeric literals
    separable.

    Both halves are `rfl` now, where the string pair needed a `funext` and a case split: the
    codec *is* the restriction, rather than a hand-written pair that agreed with one. -/
theorem literalCodec_e_restrict (k : GroundKind) (x : k.Carrier) :
    (literalCodec k x).e = ((baseCodec k).restrict (inL k x)).e := rfl

theorem literalCodec_p_restrict (k : GroundKind) (x : k.Carrier) :
    (literalCodec k x).p = ((baseCodec k).restrict (inL k x)).p := rfl

/-- **A literal codec writes only its own alternative.** `restrict`'s `e` is a guard in front
    of the base's, so a defined write is the value `ℓ` names — which is what an object option's
    content admission reads off a field whose term is a literal. -/
theorem inL_of_literalCodec_e {k : GroundKind} {x : k.Carrier} {v a}
    (he : (literalCodec k x).e v = some a) : inL k x v = true := by
  rw [literalCodec_e_restrict] at he
  simp only [Codec.restrict] at he
  split at he
  · assumption
  · exact absurd he (by simp)

/-- The member is the base's, and the base's is the index's. -/
theorem literalCodec_μ (k : GroundKind) (x : k.Carrier) :
    (literalCodec k x).μ = some k.member := by cases k <;> rfl

/-- The value `ℓ` names places the value in the held set — the direction `Carrier` needs.

    The four ungated bases are the payload equality outright. `number` and `decimal` reach here
    with a `dite` on their gate, so the branch splits on the gate and names the alternative as a
    subtype, and `toValue` projects it straight back. `cases hs :` rather than `by_cases`, which
    is classical. `.null` is `rfl`: it used to need the alternative set's nonemptiness proof, and
    a carrier with one inhabitant needs nothing. -/
theorem hLit_of_inL (k : GroundKind) (x : k.Carrier) (v : Value) :
    inL k x v = true → HLit k x v := by
  cases k <;> cases v <;> intro h <;>
    first
      | exact Bool.noConfusion h
      | rfl
      | (simp only [inL, decide_eq_true_eq] at h
         subst h
         rfl)
      | (simp only [inL] at h
         split at h
         · simp only [decide_eq_true_eq] at h
           subst h
           rfl
         · exact Bool.noConfusion h)
      | (rename_i d
         cases hs : Numeral.WF d.toDec with
         | true =>
           simp only [inL, hs, dif_pos, decide_eq_true_eq] at h
           exact congrArg Value.num (congrArg Subtype.val h)
         | false => simp [inL, hs] at h)

/-- `alternate reader`: extend the reading. With §3's coherence premise this presentation equals
    the order-free `p ∪ r`. -/
def Codec.extendRead (c : Codec) (r : Attr → Option Value) : Codec :=
  { T := c.T
    μ := c.μ
    e := c.e
    p := fun a => match c.p a with | some v => some v | none => r a }

/-! ### What the wrappers write and read

Each wrapper is one line of definition and touches exactly one half of the pair; stating
that as an `iff` is what keeps the proofs below — and §6's wrapper rows — from unfolding
the definitions again. `held` and `alternate reader` are transparent on the side they do not
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

/-- `alternate reader` does not touch the writing at all — §5's whole point. -/
theorem extendRead_e {r : Attr → Option Value} {v a} :
    (c.extendRead r).e v = some a ↔ c.e v = some a := Iff.rfl

/-- It reads through the base where the base reads, and through the migration exactly
    where the base does not. That "exactly" is where canonical reads go. -/
theorem extendRead_p {r : Attr → Option Value} {a v} :
    (c.extendRead r).p a = some v ↔ c.p a = some v ∨ (c.p a = none ∧ r a = some v) := by
  show (match c.p a with | some w => some w | none => r a) = some v ↔ _
  cases hp : c.p a <;> simp

end WrapperInversion

/-- Lawfulness sees only the pair and the member, so it transfers to any codec agreeing on
    those three. This is how a ground codec inherits from the wrapper it turns out to be,
    without disturbing its definition — which matters, since the definitions are unfolded
    all over the development. -/
theorem Lawful.congr {c d : Codec} (he : c.e = d.e) (hp : c.p = d.p) (hμ : c.μ = d.μ)
    (h : Lawful d) : Lawful c := by
  refine ⟨?_, ?_, ?_⟩
  · intro t a hx; rw [he] at hx; rw [hp]; exact h.retract hx
  · intro a t hx; rw [hp] at hx; rw [he]; exact h.canon hx
  · intro μ hm t a hx; rw [hμ] at hm; rw [he] at hx; exact h.writes hm hx

/-- The carrier transfers too, given the held set is no smaller. -/
theorem Carrier.congr {c d : Codec} (he : c.e = d.e) (hp : c.p = d.p)
    (hT : ∀ v, d.T v → c.T v) (h : Carrier d) : Carrier c := by
  refine ⟨?_, ?_⟩
  · intro v a hx; rw [he] at hx; exact hT v (h.domE hx)
  · intro a v hx; rw [hp] at hx; exact hT v (h.ranP hx)

/-- Forgetting the member index preserves the laws — `(lazy)` concludes `⊤`. -/
theorem Lawful.μNone {c : Codec} (h : Lawful c) : Lawful { c with μ := none } := by
  refine ⟨h.retract, h.canon, ?_⟩
  intro _ h'
  exact nomatch h'

theorem LawfulCore.μNone {c : Codec} (h : LawfulCore c) :
    LawfulCore { c with μ := none } := by
  refine ⟨h.retract, h.canon, ?_⟩
  intro _ h'
  exact nomatch h'

end

end Calculus
