import Calculus.Denote

/-!
# Continuity of `union`

Every least-fixpoint construction discharges a **monotonicity obligation**: unfolding may only
add information. `altCodec` resolves by the first admitter, so growth of an option changes the
union's answer only where two admitters disagree. Under the obligation that every admitter agrees
(`ConfluentAt`), first-match resolution is monotone (`selectF_mono_list`) and continuous
(`selectF_continuous_list`). A codec built to break the obligation (`optBad_not_confluent`) shows
that the obligation is not free.
-/

namespace Calculus

/-! ## The information order

The minimal requirement *any* such ccpo must meet — `e` and `p` grow from undefined, with
`Codec.empty` at the bottom — stated positively, so nothing here depends on which ccpo one
picks. -/
structure Codec.Approx (c c' : Codec) : Prop where
  /-- Everything `c` encodes, `c'` encodes the same way. -/
  e : ∀ {v a}, c.e v = some a → c'.e v = some a
  /-- Everything `c` decodes, `c'` decodes the same way. -/
  p : ∀ {a v}, c.p a = some v → c'.p a = some v

theorem Codec.Approx.refl (c : Codec) : Codec.Approx c c :=
  ⟨fun h => h, fun h => h⟩

/-- `Codec.empty` is below everything: the bottom of any such order, and what a staged
    definition would start from. -/
theorem Codec.Approx.empty_le (c : Codec) : Codec.Approx Codec.empty c := by
  refine ⟨?_, ?_⟩ <;> intro _ _ h <;> exact nomatch h

/-! ## The witnesses -/

/-- The stable option: `literal("A")`, which admits `"A"` at every stage. -/
noncomputable def optLit : Codec := (literalCodec .string "A")

/-- The growing option, before unfolding: undefined everywhere. -/
def optBot : Codec := Codec.empty

/-! ## What *is* monotone, and why the contrast is the whole point

    Two of the three wrappers §5 calls one-sided move cleanly in the information order: one up,
    one down. -/

/-- **`alternate reader` is a step up.** `extendRead` only ever adds readings — everything `c`
    decodes, the migration decodes the same way, and the writing half is untouched. §3's
    `(alternate reader)` coherence premise is what makes this an *extension* rather than a
    replacement, and this is that fact in the information order. -/
theorem approx_extendRead (c : Codec) (r : Attr → Option Value) :
    Codec.Approx c (c.extendRead r) :=
  ⟨fun h => h, fun h => by simp only [Alg.Codec.extendRead, h]⟩

/-- **`refine` is a step down.** The prism only ever removes, on both halves — which is
    why §6's `refine(c, T) ≡ c` is the top of a descending chain and not a coincidence. -/
theorem approx_restrict (c : Codec) (q : Value → Bool) :
    Codec.Approx (c.restrict q) c :=
  ⟨fun h => (restrict_e.mp h).2, fun h => (restrict_p.mp h).1⟩

/-! ## First-match resolution under the obligation

The definition takes the first admitter and never compares attributes, so no `DecidableEq Attr`
is needed (undecidable through `Attr.m`'s function field). The obligation says that the choice
did not matter, and order-independence is recovered as a theorem. -/

/-- First-match resolution, value side. Total on the union of the options' domains. -/
def selectF (os : List Codec) (v : Value) : Option Attr :=
  select os (·.e) v

/-- The obligation at one input: every admitter writes the same attribute. -/
def ConfluentAt (os : List Codec) (v : Value) : Prop :=
  ∀ o ∈ os, ∀ o' ∈ os, (o.e v).isSome = true → (o'.e v).isSome = true → o.e v = o'.e v

/-- `selectF`, reduced at an admitting head. -/
theorem selectF_admit {o : Codec} {os : List Codec} {v : Value}
    (h : (o.e v).isSome = true) : selectF (o :: os) v = o.e v := by
  simp [selectF, select, List.find?, h]

/-- …and at a non-admitting one. -/
theorem selectF_skip {o : Codec} {os : List Codec} {v : Value}
    (h : (o.e v).isSome = false) : selectF (o :: os) v = selectF os v := by
  simp [selectF, select, List.find?, h]

/-! ### The obligation is not free, and a new witness is needed -/

/-- A pair that writes `⟨S,"B"⟩` where the literal writes `⟨S,"A"⟩`. -/
def ceBad : Value → Option Attr :=
  fun v => match v with | .str "A" => some (.s "B") | _ => none

/-- …as a codec, and `Codec.empty` approximates it, so the growth is legitimate. -/
def cBad : Codec :=
  { T := fun v => (ceBad v).isSome, μ := none, e := ceBad, p := fun _ => none }

/-- …as an option. -/
def optBad : Codec := cBad

/-- **The counterexample the obligation excludes**: with the growing option first, the answer
    **changes**, `⟨S,"A"⟩` to `⟨S,"B"⟩`. -/
theorem selectF_not_monotone :
    selectF [optBot, optLit] (.str "A") = some (.s "A")
    ∧ selectF [optBad, optLit] (.str "A") = some (.s "B") := by
  constructor <;>
    simp [selectF, select, optBot, optBad, optLit, cBad, ceBad, Codec.empty,
          literalCodec, baseCodec, Alg.Codec.restrict, inL, stringCodec]

/-- …and the obligation is exactly what that violates. -/
theorem optBad_not_confluent : ¬ ConfluentAt [optBad, optLit] (.str "A") := by
  intro h
  have := h optBad (by simp) optLit (by simp)
    (by simp [optBad, cBad, ceBad])
    (by simp [optLit, literalCodec, baseCodec, Alg.Codec.restrict, inL,
              stringCodec])
  simp [optBad, optLit, cBad, ceBad, literalCodec, baseCodec,
        Alg.Codec.restrict, inL, stringCodec] at this

/-! **The ground-term witness is gone, and it was the decimal conflation.** ~~string_decimal_not_confluent~~
took `string` and a decimal base both writing `.str "1.5"` and storing it differently. The model
has no decimal base now, and no ground term writes text and stores `N`. The host's decimal is
`held` over `number`, and `held` is not a ground term. So no ground pair is a witness, and
the theorem is false rather than unproved.

What the section still records is `optBad_not_confluent` above, which uses a codec built to break
the obligation. So confluence is still not automatic, and is still an invariant the unrolling must
carry. What is no longer true is that a pair of ORDINARY GROUND TERMS witnesses the failure. That
is a consequence of separating the carrier from the wire, not an argument that no ground witness
remains; none is claimed here. -/

/-! ### The two obligations a least fixpoint discharges -/

/-- **Monotonicity.** Stated with the growing option first — the
    only position where growth can change the answer, since grown second the earlier admitter
    answers throughout. Confluence is used in exactly one of the three cases: where growth newly
    admits at a value another option was already answering. -/
theorem selectF_mono {o₁ o₁' o₂ : Codec} {v : Value} {a : Attr}
    (hap : Codec.Approx o₁ o₁')
    (hc : ConfluentAt [o₁', o₂] v)
    (h : selectF [o₁, o₂] v = some a) : selectF [o₁', o₂] v = some a := by
  have hadm : (o₁.e v).isSome = true → (o₁'.e v).isSome = true := fun h1 =>
    let ⟨b, hb⟩ := Option.isSome_iff_exists.mp h1
    by rw [hap.e hb]; rfl
  cases h1' : (o₁'.e v).isSome with
  | false =>
    have h1 : (o₁.e v).isSome = false := by
      cases h1 : (o₁.e v).isSome with
      | true => rw [hadm h1] at h1'; exact nomatch h1'
      | false => rfl
    rw [selectF_skip h1']; rw [selectF_skip h1] at h; exact h
  | true =>
    cases h1 : (o₁.e v).isSome with
    | true => rw [selectF_admit h1']; rw [selectF_admit h1] at h; exact hap.e h
    | false =>
      rw [selectF_admit h1']; rw [selectF_skip h1] at h
      cases h2 : (o₂.e v).isSome with
      | false => rw [selectF_skip h2] at h; exact nomatch h
      | true =>
        rw [selectF_admit h2] at h
        rw [hc o₁' (by simp) o₂ (by simp) h1' h2]; exact h

/-- Directed continuity, stated **without constructing sups** — this file defines `Codec.Approx`
    and deliberately no ccpo. `oω` is an upper bound that is *least at `v`*: every answer
    it gives, some finite stage already gave. In the flat `Option` order that is the whole sup
    condition. -/
structure IsSupAt (f : Nat → Codec) (oω : Codec) (v : Value) : Prop where
  /-- an upper bound of the chain -/
  ub : ∀ i, Codec.Approx (f i) oω
  /-- …and least at `v`: the limit adds no answer the chain did not have -/
  least : ∀ a, oω.e v = some a → ∃ i, (f i).e v = some a

/-- **Continuity — with the growing option first, needing no confluence.** That arrangement is
    load-bearing and the general case does not share it: see `selectF_continuous_list`, which
    takes the obligation at each stage. Growth-first is automatically the first admitter, so no
    other option can answer; elsewhere in the list the obligation is what says they agree. -/
theorem selectF_continuous {f : Nat → Codec} {oω o₂ : Codec} {v : Value} {a : Attr}
    (hs : IsSupAt f oω v)
    (h : selectF [oω, o₂] v = some a) : ∃ i, selectF [f i, o₂] v = some a := by
  have hadm : ∀ i, ((f i).e v).isSome = true → (oω.e v).isSome = true := fun i h1 =>
    let ⟨b, hb⟩ := Option.isSome_iff_exists.mp h1
    by rw [(hs.ub i).e hb]; rfl
  cases hω : (oω.e v).isSome with
  | true =>
    rw [selectF_admit hω] at h
    obtain ⟨i, hi⟩ := hs.least a h
    exact ⟨i, by rw [selectF_admit (by rw [hi]; rfl)]; exact hi⟩
  | false =>
    refine ⟨0, ?_⟩
    have h0 : ((f 0).e v).isSome = false := by
      cases h0 : ((f 0).e v).isSome with
      | true => rw [hadm 0 h0] at hω; exact nomatch hω
      | false => rfl
    rw [selectF_skip h0]; rw [selectF_skip hω] at h; exact h


/-- Confluence is inherited by a tail. -/
theorem ConfluentAt.tail {o : Codec} {os : List Codec} {v : Value}
    (h : ConfluentAt (o :: os) v) : ConfluentAt os v :=
  fun a ha b hb => h a (by simp [ha]) b (by simp [hb])

/-- The answer `selectF` gives comes from a member that admits. -/
theorem selectF_mem : ∀ {os : List Codec} {v : Value} {a : Attr},
    selectF os v = some a → ∃ o ∈ os, (o.e v).isSome = true ∧ o.e v = some a
  | [], _, _, h => absurd h (by simp [selectF, select])
  | o :: os, v, a, h => by
      cases ho : (o.e v).isSome with
      | true => exact ⟨o, by simp, ho, by rw [selectF_admit ho] at h; exact h⟩
      | false =>
        rw [selectF_skip ho] at h
        obtain ⟨o', ho', hadm, he⟩ := selectF_mem h
        exact ⟨o', by simp [ho'], hadm, he⟩

/-- **Order-independence as a theorem.** Under the obligation, *any* admitter's answer is the
    answer — so the first-match definition does not depend on the order after all. -/
theorem selectF_of_mem : ∀ {os : List Codec} {v : Value} {o : Codec},
    ConfluentAt os v → o ∈ os → (o.e v).isSome = true → selectF os v = o.e v
  | [], _, _, _, ho, _ => absurd ho (by simp)
  | hd :: tl, v, o, hc, ho, hadm => by
      cases hhd : (hd.e v).isSome with
      | true =>
        rw [selectF_admit hhd]
        exact hc hd (by simp) o (by simp [ho]) hhd hadm
      | false =>
        rw [selectF_skip hhd]
        have hne : o ≠ hd := fun h => by rw [h, hhd] at hadm; exact nomatch hadm
        exact selectF_of_mem (ConfluentAt.tail hc) (by
          rcases List.mem_cons.mp ho with rfl | h'
          · exact absurd rfl hne
          · exact h') hadm


/-! ### The general list versions

With the growing option first, it is the first admitter, so no other option can answer. Anywhere
else in the list, the obligation says that the first admitter agrees with the one that grew. So
the obligation must hold at every stage, and that one requirement buys both monotonicity and
continuity. -/

/-- **Monotonicity over an arbitrary option list**, with the growth as a map. Cleaner than the
    two-option case, because `selectF_of_mem` does the work: the answer comes from *some*
    admitting member (`selectF_mem`), that member grows to an admitter with the same answer, and
    under the obligation any admitter's answer is the answer. -/
theorem selectF_mono_list {os : List Codec} {g : Codec → Codec}
    {v : Value} {a : Attr}
    (hap : ∀ o ∈ os, Codec.Approx o (g o))
    (hc : ConfluentAt (os.map g) v)
    (h : selectF os v = some a) : selectF (os.map g) v = some a := by
  obtain ⟨o, ho, -, hoe⟩ := selectF_mem h
  have hmem : g o ∈ os.map g := List.mem_map_of_mem ho
  rw [selectF_of_mem hc hmem (by rw [(hap o ho).e hoe]; rfl)]
  exact (hap o ho).e hoe

/-- **Continuity, in general — and it does need the obligation at each stage.** See the note
    above: `selectF_continuous` escaped it by putting the growing option first. -/

theorem selectF_continuous_list {os : List Codec} {F : Nat → Codec → Codec}
    {v : Value} {a : Attr}
    (hleast : ∀ o ∈ os, ∀ b, o.e v = some b → ∃ i, (F i o).e v = some b)
    (hc : ∀ i, ConfluentAt (os.map (F i)) v)
    (h : selectF os v = some a) : ∃ i, selectF (os.map (F i)) v = some a := by
  obtain ⟨o, ho, hoadm, hoe⟩ := selectF_mem h
  obtain ⟨i, hi⟩ := hleast o ho a hoe
  refine ⟨i, ?_⟩
  have hmem : F i o ∈ os.map (F i) := List.mem_map_of_mem ho
  rw [selectF_of_mem (hc i) hmem (by rw [hi]; rfl)]
  exact hi

/-! ### What this does and does not establish

**Does:** under the obligation, first-match resolution is monotone and continuous, the two
obligations a least-fixpoint construction discharges.

**Does not:** construct a fixpoint. This file defines no ccpo. The model constructs its
recursive terms another way: `mu` and `opaque` denote `muCodec` (`Recursion.lean`), which reads
each input at the stage its own depth names. That construction needs no monotone chain, and so
none of the obligations here: the guard of the binder alone makes the stages agree past the
depth of the input.

Under a least-fixpoint construction the obligation would have to be an invariant of the
unrolling, and `optBad_not_confluent` is the witness that it is not free. -/

end Calculus
