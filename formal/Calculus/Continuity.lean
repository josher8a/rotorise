import Calculus.Denote

/-!
# Non-continuity of `union` — why a fixpoint definition is impossible

Every least-fixpoint construction discharges a **monotonicity obligation**: unfolding may only
add information. `altCodec` resolves by *unique* admission, so as the recursive results grow,
admission grows, the filtered list grows from `[o]` to `[o, o']`, and the answer collapses from
`some` to `none`. (U) is a negative condition on the *other* options — anti-monotone in exactly
the argument a fixpoint must grow.

The consequence for the specification, which is why this file sits beside `Discharge.lean`: a
union whose options are genuinely recursive has no fixpoint semantics **under this resolution
rule**, so `lazy` under `union` is unmodelled rather than merely awkward.

**The scope is load-bearing: this is refuted by (U) specifically**, unique admission being a
**negative** condition on the other options — so the refutation is about the *rule*, not about
the constructor. The last section is the demonstration: weaken (U) to *confluence*, where every
admitter agrees rather than exactly one admitting, and monotonicity comes back —
`altCodec_not_monotone`'s own witness has its two admitters agreeing.

The full argument is below and in commit `7ed4e5e` — the ccpo obligation, the direction of
failure, the relational route, and what a port to Isabelle/HOL would meet instead.
-/

namespace Calculus

/-! ## The information order

The minimal requirement *any* such ccpo must meet — `e` and `p` grow from undefined, with
`Codec.empty` at the bottom — stated positively, so the refutation does not depend on which
ccpo one picks. -/
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

/-! ## The refutation, on `altCodec`

§4's counterexample pair, `union(literal("A"), string)`, with the `string` side at two stages
of definedness. -/

/-- The stable option: `literal("A")`, which admits `"A"` at every stage. -/
noncomputable def optLit : OptionSem := .byAttempt (literalCodec .string "A")

/-- The growing option, before unfolding: undefined everywhere. -/
def optBot : OptionSem := .byAttempt Codec.empty

/-- The growing option, after unfolding: `string`, which now also admits `"A"`. -/
def optStr : OptionSem := .byAttempt stringCodec

/-- `optBot` approximates `optStr` — the growing option only ever gained information. -/
theorem optBot_approx_optStr : Codec.Approx optBot.c optStr.c :=
  Codec.Approx.empty_le _

/-- **The obligation `partial_function` cannot discharge.** One option grows in the
    information order and the union's `e` *shrinks*. No ccpo repairs it: the order above is a
    consequence of having a fixpoint at all. -/
theorem altCodec_not_monotone :
    Codec.Approx optBot.c optStr.c
    ∧ (altCodec [optLit, optBot] (some .S)).e (.str "A") = some (.s "A")
    ∧ (altCodec [optLit, optStr] (some .S)).e (.str "A") = none := by
  refine ⟨optBot_approx_optStr, ?_, ?_⟩ <;>
    simp [altCodec, select, optLit, optBot, optStr, OptionSem.byAttempt,
          literalCodec, baseCodec, Codec.restrict, inL, stringCodec, Codec.empty]

/-! ## The same defect through a staged denotation

`denote` is structural and does not stage, so the collapse below is shown on a staged
denotation built for the purpose rather than on `denote` itself — and *why* `denote` need not
stage is the same fact this file is about. `Term.lazy` carries a plain `Term`, not a thunk,
precisely because a genuinely recursive union has no fixpoint semantics (the refutation
above). There is no recursion to approximate, so there is no
approximation to be non-monotone.

The theorem is kept, restated over a staging defined **here**, as a witness construction rather
than as the denotation. That is the honest shape: the staged function is what a fixpoint
definition of `denote` would have had to be, and the theorem says it cannot be one. -/

/-- The staged approximation a fixpoint definition of `denote` would need, at the shape the
    witness uses. Everything else is `Codec.empty`: this is a witness, not a semantics. -/
noncomputable def stage : Nat → Term → Codec
  | 0, _ => Codec.empty
  | _+1, .literal k ls => literalCodec k ls
  | _+1, .string => stringCodec
  | n+1, .lazy t => { stage n t with μ := none }
  | n+1, .union opts =>
      altCodec (opts.map fun t => optionSemOf (stage n t) (specOf t))
        (unanimous (opts.map fun t => (stage n t).μ))
  | _+1, _ => Codec.empty

/-- §4's `union(literal("A"), string)`, with the `string` option behind a `lazy` so it
    arrives one stage later than the literal. -/
def tWitness : Term :=
  .union [.literal .string "A", .lazy .string]

/-- **The stages are not a chain.** Stage `2` encodes `"A"`; stage `3` encodes nothing. So
    `⨆ n, stage n t` is not a definition either, and the low-stage answer is *over*-defined —
    a different answer, not an approximation from below. -/
theorem stage_not_monotone :
    (stage 2 tWitness).e (.str "A") = some (.s "A")
    ∧ (stage 3 tWitness).e (.str "A") = none := by
  constructor <;>
    simp [stage, tWitness, specOf, optionSemOf, altCodec, select, OptionSem.byAttempt,
          literalCodec, baseCodec, Codec.restrict, inL, stringCodec, Codec.empty]

/-- At stage `3` the union is simply the ill-formed one §4 refuted, and `none` is correct;
    stage `2` hid that by not looking. The defect is not a wrong answer at stage `3` — it is
    that no monotone approximation exists, (U) being a property of the whole option list. -/
theorem tWitness_violates_uniqueAdmission :
    ((stage 3 tWitness).e (.str "A")).isNone := by
  simp [stage_not_monotone.2]

/-! ## What *is* monotone, and why the contrast is the whole point

    The refutation above is about `union`, and it is worth saying plainly that it is not
    about the calculus. Two of the three wrappers §5 calls one-sided move cleanly in the
    information order — one up, one down — and it is the *sum* that moves neither way.

    So "a codec is a continuous map between information lattices" is a reading the
    wrappers support and the sum refutes. It is refuted by (U) specifically: unique
    admission is a **negative** condition on the other options, so growth anywhere in the
    list can remove definedness everywhere. Nothing about partiality or the quotient is
    responsible; a calculus with both and no sum would be continuous. -/

/-- **`legacy` is a step up.** `extendRead` only ever adds readings — everything `c`
    decodes, the migration decodes the same way, and the writing half is untouched. §3's
    `(legacy)` coherence premise is what makes this an *extension* rather than a
    replacement, and this is that fact in the information order. -/
theorem approx_extendRead (c : Codec) (r : Attr → Option Value) :
    Codec.Approx c (c.extendRead r) :=
  ⟨fun h => h, fun h => by simp only [Codec.extendRead, h]⟩

/-- **`refine` is a step down.** The prism only ever removes, on both halves — which is
    why §6's `refine(c, T) ≡ c` is the top of a descending chain and not a coincidence. -/
theorem approx_restrict (c : Codec) (q : Value → Bool) :
    Codec.Approx (c.restrict q) c :=
  ⟨fun h => (restrict_e.mp h).2, fun h => (restrict_p.mp h).1⟩

/-! ## The condition, weakened — and what it restores

Everything above is about **unique** admission. Weaken it to **confluence** — *every* admitter
agrees, rather than *exactly one* admits — and the picture changes, because the negative
condition becomes a positive one.

Stating it as first-match plus an obligation is what makes it usable: the *definition* takes the
first admitter and never compares attributes, so no `DecidableEq Attr` is needed (undecidable
through `Attr.m`'s function field, and noncomputable through `Double` besides), while the
*obligation* says the choice did not matter. So the order-independence that looks lost is
recovered as a theorem — which places this exactly between the two designs: first-match with no
obligation is order-dependent, unique admission needs no obligation and is partial. -/

/-- First-match resolution, value side. Total on the union of the options' domains. -/
def selectF (os : List OptionSem) (v : Value) : Option Attr :=
  match os.filter (fun o => o.admitV v) with
  | [] => none
  | o :: _ => o.c.e v

/-- The obligation at one input: every admitter writes the same attribute. Weaker than (U),
    which demands there be only one. -/
def ConfluentAt (os : List OptionSem) (v : Value) : Prop :=
  ∀ o ∈ os, ∀ o' ∈ os, o.admitV v = true → o'.admitV v = true → o.c.e v = o'.c.e v

/-- `selectF`, reduced at an admitting head. -/
theorem selectF_admit {o : OptionSem} {os : List OptionSem} {v : Value}
    (h : o.admitV v = true) : selectF (o :: os) v = o.c.e v := by
  simp [selectF, h]

/-- …and at a non-admitting one. -/
theorem selectF_skip {o : OptionSem} {os : List OptionSem} {v : Value}
    (h : o.admitV v = false) : selectF (o :: os) v = selectF os v := by
  simp [selectF, h]

/-- **`altCodec_not_monotone`'s witness does not refute confluence.** The growing option is
    `string` and the fixed one is `literal("A")`; at `"A"` both admit and **both write
    `⟨S,"A"⟩`**. Under counting the answer collapses from `some` to `none` — that is the
    refutation. Under confluence it stays. -/
theorem confluent_survives_the_refutation :
    optLit.c.e (.str "A") = optStr.c.e (.str "A") := by
  simp [optLit, optStr, OptionSem.byAttempt, literalCodec, baseCodec, Codec.restrict, inL,
        stringCodec]

/-! ### The obligation is not free, and a new witness is needed -/

/-- A pair that writes `⟨S,"B"⟩` where the literal writes `⟨S,"A"⟩`. -/
def ceBad : Value → Option Attr :=
  fun v => match v with | .str "A" => some (.s "B") | _ => none

/-- …as a codec, and `Codec.empty` approximates it, so the growth is legitimate. -/
def cBad : Codec :=
  { T := fun v => (ceBad v).isSome, μ := none, e := ceBad, p := fun _ => none }

/-- …as an option. -/
def optBad : OptionSem := .byAttempt cBad

/-- **The counterexample confluence still needs**, and the failure mode differs from
    counting's: with the growing option *first*, the answer does not collapse to `none`, it
    **changes** — `⟨S,"A"⟩` to `⟨S,"B"⟩`. So `selectF` alone is no better than `select`; it is
    `selectF` *under the obligation* that is. -/
theorem selectF_not_monotone :
    selectF [optBot, optLit] (.str "A") = some (.s "A")
    ∧ selectF [optBad, optLit] (.str "A") = some (.s "B") := by
  constructor <;>
    simp [selectF, optBot, optBad, optLit, OptionSem.byAttempt, cBad, ceBad, Codec.empty,
          literalCodec, baseCodec, Codec.restrict, inL, stringCodec]

/-- …and the obligation is exactly what that violates. -/
theorem optBad_not_confluent : ¬ ConfluentAt [optBad, optLit] (.str "A") := by
  intro h
  have := h optBad (by simp) optLit (by simp)
    (by simp [optBad, OptionSem.byAttempt, cBad, ceBad])
    (by simp [optLit, OptionSem.byAttempt, literalCodec, baseCodec, Codec.restrict, inL,
              stringCodec])
  simp [optBad, optLit, OptionSem.byAttempt, cBad, ceBad, literalCodec, baseCodec,
        Codec.restrict, inL, stringCodec] at this

/-- **Nor is the obligation automatic at ground terms.** `string` and `decimal` both take the
    value `.str "1.5"` and store it *differently*. Neither is an escape hatch. So confluence has
    to be an **invariant of the unrolling**, which is the residue this section leaves: it holds
    vacuously wherever the options are pairwise disjoint, and a syntactic disjointness check
    (`Orth`, `Orthogonality.lean`) is what would license that. -/
theorem string_decimal_not_confluent :
    ¬ ConfluentAt [.byAttempt (denote .string), .byAttempt (denote .decimal)] (.str "1.5") := by
  intro h
  have hs : (OptionSem.byAttempt (denote .string)).admitV (.str "1.5") = true := by
    simp [OptionSem.byAttempt, denote, stringCodec]
  have hd : (OptionSem.byAttempt (denote .decimal)).admitV (.str "1.5") = true := by
    simp [OptionSem.byAttempt, denote, decimalCodec]; decide
  have := h _ (by simp) _ (by simp) hs hd
  simp [OptionSem.byAttempt, denote, stringCodec, decimalCodec] at this

/-! ### The two obligations a least fixpoint discharges -/

/-- **Monotonicity, which counting provably lacks.** Stated with the growing option first — the
    only position where growth can change the answer, since grown second the earlier admitter
    answers throughout. Confluence is used in exactly one of the three cases: where growth newly
    admits at a value another option was already answering. -/
theorem selectF_mono {o₁ o₁' o₂ : OptionSem} {v : Value} {a : Attr}
    (hap : Codec.Approx o₁.c o₁'.c)
    (hadm : o₁.admitV v = true → o₁'.admitV v = true)
    (hc : ConfluentAt [o₁', o₂] v)
    (h : selectF [o₁, o₂] v = some a) : selectF [o₁', o₂] v = some a := by
  cases h1' : o₁'.admitV v with
  | false =>
    have h1 : o₁.admitV v = false := by
      cases h1 : o₁.admitV v with
      | true => rw [hadm h1] at h1'; exact nomatch h1'
      | false => rfl
    rw [selectF_skip h1']; rw [selectF_skip h1] at h; exact h
  | true =>
    cases h1 : o₁.admitV v with
    | true => rw [selectF_admit h1']; rw [selectF_admit h1] at h; exact hap.e h
    | false =>
      rw [selectF_admit h1']; rw [selectF_skip h1] at h
      cases h2 : o₂.admitV v with
      | false => rw [selectF_skip h2] at h; exact nomatch h
      | true =>
        rw [selectF_admit h2] at h
        rw [hc o₁' (by simp) o₂ (by simp) h1' h2]; exact h

/-- Directed continuity, stated **without constructing sups** — this file defines `Codec.Approx`
    and deliberately no ccpo, so that the refutation does not depend on which one is picked, and
    the same restraint applies here. `oω` is an upper bound that is *least at `v`*: every answer
    it gives, some finite stage already gave. In the flat `Option` order that is the whole sup
    condition. -/
structure IsSupAt (f : Nat → OptionSem) (oω : OptionSem) (v : Value) : Prop where
  /-- an upper bound of the chain -/
  ub : ∀ i, Codec.Approx (f i).c oω.c
  /-- …and least at `v`: the limit adds no answer the chain did not have -/
  least : ∀ a, oω.c.e v = some a → ∃ i, (f i).c.e v = some a

/-- **Continuity — with the growing option first, needing no confluence.** That arrangement is
    load-bearing and the general case does not share it: see `selectF_continuous_list`, which
    takes the obligation at each stage. Growth-first is automatically the first admitter, so no
    other option can answer; elsewhere in the list the obligation is what says they agree.

    Counting is continuous *unconditionally* — its singleton requirement at the limit forces
    uniqueness at every earlier stage — and cannot be monotone at all. So the obligation is what
    buys monotonicity and, in general, continuity too.

    The two premises are the model's own: `hself` is `uniqueAdmission_of_disjoint`'s `hw` — a
    canonical pair admits its *own* option — and `hadm` is `byAttempt`'s definition, trivial for
    `byStructure`. -/
theorem selectF_continuous {f : Nat → OptionSem} {oω o₂ : OptionSem} {v : Value} {a : Attr}
    (hs : IsSupAt f oω v)
    (hself : ∀ i, ∀ b, (f i).c.e v = some b → (f i).admitV v = true)
    (hadm : ∀ i, (f i).admitV v = true → oω.admitV v = true)
    (h : selectF [oω, o₂] v = some a) : ∃ i, selectF [f i, o₂] v = some a := by
  cases hω : oω.admitV v with
  | true =>
    rw [selectF_admit hω] at h
    obtain ⟨i, hi⟩ := hs.least a h
    exact ⟨i, by rw [selectF_admit (hself i a hi)]; exact hi⟩
  | false =>
    refine ⟨0, ?_⟩
    have h0 : (f 0).admitV v = false := by
      cases h0 : (f 0).admitV v with
      | true => rw [hadm 0 h0] at hω; exact nomatch hω
      | false => rfl
    rw [selectF_skip h0]; rw [selectF_skip hω] at h; exact h


/-- Confluence is inherited by a tail. -/
theorem ConfluentAt.tail {o : OptionSem} {os : List OptionSem} {v : Value}
    (h : ConfluentAt (o :: os) v) : ConfluentAt os v :=
  fun a ha b hb => h a (by simp [ha]) b (by simp [hb])

/-- The answer `selectF` gives comes from a member that admits. -/
theorem selectF_mem : ∀ {os : List OptionSem} {v : Value} {a : Attr},
    selectF os v = some a → ∃ o ∈ os, o.admitV v = true ∧ o.c.e v = some a
  | [], _, _, h => absurd h (by simp [selectF])
  | o :: os, v, a, h => by
      cases ho : o.admitV v with
      | true => exact ⟨o, by simp, ho, by rw [selectF_admit ho] at h; exact h⟩
      | false =>
        rw [selectF_skip ho] at h
        obtain ⟨o', ho', hadm, he⟩ := selectF_mem h
        exact ⟨o', by simp [ho'], hadm, he⟩

/-- **Order-independence as a theorem.** Under the obligation, *any* admitter's answer is the
    answer — so the first-match definition does not depend on the order after all. -/
theorem selectF_of_mem : ∀ {os : List OptionSem} {v : Value} {o : OptionSem},
    ConfluentAt os v → o ∈ os → o.admitV v = true → selectF os v = o.c.e v
  | [], _, _, _, ho, _ => absurd ho (by simp)
  | hd :: tl, v, o, hc, ho, hadm => by
      cases hhd : hd.admitV v with
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


/-! ### The general list versions, and a correction they force

The two theorems above are the two-option, growth-first case. Generalising them changes one
claim: `selectF_continuous`'s docstring said continuity "needs no confluence". **That is true of
growth-first and false in general** — with the growing option first it is automatically the first
admitter, so no other option can answer; anywhere else in the list, the obligation is what says
the first admitter agrees with the one that grew.

Counting is the reverse: its continuity really is unconditional, because its own singleton
requirement *at the limit* forces uniqueness at every earlier stage (admission only grows, so the
filter is `[o]` or `[]`). So the corrected diagnosis is simpler than the one it replaces —
**the obligation must hold at every stage, and that one requirement buys both** monotonicity and
continuity, where counting gets continuity free and cannot have monotonicity at all. -/

/-- **Monotonicity over an arbitrary option list**, with the growth as a map. Cleaner than the
    two-option case, because `selectF_of_mem` does the work: the answer comes from *some*
    admitting member (`selectF_mem`), that member grows to an admitter with the same answer, and
    under the obligation any admitter's answer is the answer. -/
theorem selectF_mono_list {os : List OptionSem} {g : OptionSem → OptionSem}
    {v : Value} {a : Attr}
    (hap : ∀ o ∈ os, Codec.Approx o.c (g o).c)
    (hadm : ∀ o ∈ os, o.admitV v = true → (g o).admitV v = true)
    (hc : ConfluentAt (os.map g) v)
    (h : selectF os v = some a) : selectF (os.map g) v = some a := by
  obtain ⟨o, ho, hoadm, hoe⟩ := selectF_mem h
  have hmem : g o ∈ os.map g := List.mem_map_of_mem ho
  rw [selectF_of_mem hc hmem (hadm o ho hoadm)]
  exact (hap o ho).e hoe

/-- **Continuity, in general — and it does need the obligation at each stage.** See the note
    above: `selectF_continuous` escaped it by putting the growing option first. -/

theorem selectF_continuous_list {os : List OptionSem} {F : Nat → OptionSem → OptionSem}
    {v : Value} {a : Attr}
    (hself : ∀ i, ∀ o ∈ os, ∀ b, (F i o).c.e v = some b → (F i o).admitV v = true)
    (hleast : ∀ o ∈ os, ∀ b, o.c.e v = some b → ∃ i, (F i o).c.e v = some b)
    (hc : ∀ i, ConfluentAt (os.map (F i)) v)
    (h : selectF os v = some a) : ∃ i, selectF (os.map (F i)) v = some a := by
  obtain ⟨o, ho, hoadm, hoe⟩ := selectF_mem h
  obtain ⟨i, hi⟩ := hleast o ho a hoe
  refine ⟨i, ?_⟩
  have hmem : F i o ∈ os.map (F i) := List.mem_map_of_mem ho
  rw [selectF_of_mem (hc i) hmem (hself i o ho a hi)]
  exact hi

/-! ### What this does and does not establish

**Does:** the refutation above is specific to counting; confluent resolution is monotone (given
the obligation) and continuous (unconditionally), which are the two obligations a least-fixpoint
construction discharges.

**Does not:** that a fixpoint *exists*. `selectF_mono_list` and `selectF_continuous_list` above
are the general versions — this paragraph said they were "the same arguments, unwritten" and
stayed that way through the commit that wrote them, thirty lines up. Monotonicity and continuity
are a fixpoint's *obligations*, not its construction: the construction needs a ccpo this
file deliberately does not define, while `denote` is structural and does not stage — `Term.lazy`
carries a plain `Term` rather than a thunk *because* the refutation was believed. Reopening
recursion means staging `denote` again, which is a larger change than these theorems.

**And the residue is one thing:** the obligation must be an invariant of the unrolling
(`string_decimal_not_confluent`). It is vacuous where the options are pairwise disjoint, so the
syntactic disjointness check is what would license it. -/

end Calculus
