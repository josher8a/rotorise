import Calculus.Denote

/-!
# Non-continuity of `union` — why a fixpoint definition is impossible

Every least-fixpoint construction discharges a **monotonicity obligation**: unfolding may only
add information. `altCodec` resolves by *unique* admission, so as the recursive results grow,
admission grows, the filtered list grows from `[o]` to `[o, o']`, and the answer collapses from
`some` to `none`. (U) is a negative condition on the *other* options — anti-monotone in exactly
the argument a fixpoint must grow.

The consequence for the specification, which is why this file sits beside `Discharge.lean`: a
union whose options are genuinely recursive has no fixpoint semantics at all, so `lazy` under
`union` is unmodelled rather than merely awkward.

`docs/codec-formalization.md` §7 carries the full argument — the ccpo obligation, the direction
of failure, the relational route, and what a port to Isabelle/HOL would meet instead.
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
noncomputable def optLit : OptionSem := .byAttempt (literalCodec .string (.of "A" ∅))

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
          literalCodec, baseCodec, Codec.restrict, inL, stringCodec, Codec.empty, NEFinset.of]

/-! ## The same defect through a staged denotation

`denote` used to take a fuel argument, and this section showed the collapse happening between
two adjacent stages of it: `lazy` staggered the `string` option by one step, fuel `2` encoded
`"A"`, fuel `3` encoded nothing.

**`denote` is structural now and does not stage**, so that presentation is no longer a statement
about it — and *why* it need not stage is the same fact this file is about. `Term.lazy` carries a
plain `Term`, not a thunk, precisely because a genuinely recursive union has no fixpoint
semantics (the refutation above). There is no recursion to approximate, so there is no
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
  .union [.literal .string (.of "A" ∅), .lazy .string]

/-- **The stages are not a chain.** Stage `2` encodes `"A"`; stage `3` encodes nothing. So
    `⨆ n, stage n t` is not a definition either, and the low-stage answer is *over*-defined —
    a different answer, not an approximation from below. -/
theorem stage_not_monotone :
    (stage 2 tWitness).e (.str "A") = some (.s "A")
    ∧ (stage 3 tWitness).e (.str "A") = none := by
  constructor <;>
    simp [stage, tWitness, specOf, optionSemOf, altCodec, select, OptionSem.byAttempt,
          literalCodec, baseCodec, Codec.restrict, inL, stringCodec, Codec.empty, NEFinset.of]

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

end Calculus
