import Calculus.Denote

/-!
# Non-continuity of `union` — why fuel is not an artefact of Lean

`docs/codec-formalization.md` §7 records fuel as a cost of Lean's structural recursion,
and names Isabelle/HOL's `partial_function` as the escape: a pure denotation, no fuel,
no "for sufficient fuel" caveat on the theorems. This file refutes that reading.

`partial_function` — and every other least-fixpoint construction, in any system — is a
fixpoint over a ccpo, and it discharges a **monotonicity obligation on the functional**:
unfolding one more step may only *add* information. `union` does not satisfy it.

The reason is `§5`'s (U). `altCodec` resolves a union by *unique* admission:

```
e v = match os.filter (·.admitV v) with | [o] => o.c.e v | _ => none
```

`OptionSem.byAttempt` derives `admitV v` from `(c.e v).isSome` — definedness of the
option's own `e`. So as the recursive results grow, admission grows, the filtered list
grows from `[o]` to `[o, o']`, and the union's answer collapses from `some` to `none`.
Unique admission quantifies over the *other* options: it is a negative condition, and
it is anti-monotone in exactly the argument a fixpoint must grow.

Two theorems, in increasing concreteness:

* `altCodec_not_monotone` — the structural cause, stated on the combinator alone. This
  is what a `partial_function` definition of `denote` would have to prove and cannot.
* `denote_not_fuel_monotone` — the same defect reached through `denote`, on a closed
  term: the fuel stages are not a chain, so `⨆ fuel, denote fuel t` is not a definition
  either.

The corollary for tooling: the obstruction is in the calculus, not in the proof
assistant. Porting to Isabelle/HOL would replace the fuel parameter with a failed `mono`
proof at the `union` case. The corollary for the specification is sharper, and is the
reason this file lives next to `Discharge.lean`: a union whose options are *genuinely*
recursive has no fixpoint semantics at all, so `lazy` under `union` is not merely
awkward to model — it is unmodelled, and (U) is what makes it so.

The relational route closes the same way: `¬∃ another option admits` is a negative
recursive occurrence, so the admission relation is not (co)inductively definable either.
-/

namespace Calculus

/-! ## The information order

Any ccpo supporting a fixpoint definition of `denote` must at least let a codec's `e`
and `p` grow from undefined — that is what "unfolding adds information" means, and
`Codec.empty` (what `denote` returns at fuel `0`) is its bottom. `Approx` is that
minimal requirement, stated positively so the refutation below does not depend on which
ccpo one picks. -/
structure Codec.Approx (c c' : Codec) : Prop where
  /-- Everything `c` encodes, `c'` encodes the same way. -/
  e : ∀ {v a}, c.e v = some a → c'.e v = some a
  /-- Everything `c` decodes, `c'` decodes the same way. -/
  p : ∀ {a v}, c.p a = some v → c'.p a = some v

theorem Codec.Approx.refl (c : Codec) : Codec.Approx c c :=
  ⟨fun h => h, fun h => h⟩

/-- `Codec.empty` is below everything: the bottom of any such order, and the value
    `denote` takes at fuel `0`. -/
theorem Codec.Approx.empty_le (c : Codec) : Codec.Approx Codec.empty c := by
  refine ⟨?_, ?_⟩ <;> intro _ _ h <;> exact nomatch h

/-! ## The refutation, on `altCodec`

The two options are §4's counterexample pair — `union(literal("A"), string)`, the one
that refuted (K) — with the `string` side shown at two stages of definedness. -/

/-- The stable option: `literal("A")`, which admits `"A"` at every stage. -/
def optLit : OptionSem := .byAttempt (literalSCodec ["A"])

/-- The growing option, before unfolding: undefined everywhere. -/
def optBot : OptionSem := .byAttempt Codec.empty

/-- The growing option, after unfolding: `string`, which now also admits `"A"`. -/
def optStr : OptionSem := .byAttempt stringCodec

/-- `optBot` approximates `optStr` — the growing option only ever gained information. -/
theorem optBot_approx_optStr : Codec.Approx optBot.c optStr.c :=
  Codec.Approx.empty_le _

/-- **The obligation `partial_function` cannot discharge.** One option grows in the
    information order, and the union's `e` *shrinks*: defined before, undefined after.
    No ccpo repairs this — the order above is a consequence of having a fixpoint at all,
    and `altCodec` is anti-monotone with respect to it. -/
theorem altCodec_not_monotone :
    Codec.Approx optBot.c optStr.c
    ∧ (altCodec [optLit, optBot] (some .S)).e (.str "A") = some (.s "A")
    ∧ (altCodec [optLit, optStr] (some .S)).e (.str "A") = none := by
  refine ⟨optBot_approx_optStr, ?_, ?_⟩ <;>
    simp [altCodec, optLit, optBot, optStr, OptionSem.byAttempt,
          literalSCodec, stringCodec, Codec.empty]

/-! ## The same defect through `denote`

`lazy` staggers the `string` option by one fuel step, so the collapse happens between
two adjacent stages of the very function whose fuel we would like to remove. -/

/-- §4's `union(literal("A"), string)`, with the `string` option behind a `lazy` so it
    arrives one fuel step later than the literal. -/
def tWitness : Term :=
  .union [.literalS ["A"], .lazy .string]

/-- **The fuel stages are not a chain.** At fuel `2` the term encodes `"A"`; at fuel `3`
    it encodes nothing. So `denote` is not monotone in fuel, `⨆ fuel, denote fuel t` is
    not a definition, and the "for sufficient fuel" hypothesis on the theorems is not
    removable by taking a limit.

    Note which way it fails: the low-fuel answer is *over*-defined, not under-defined.
    Fuel `2` answers `some` because it has not yet seen the second option — it is not a
    sound approximation of the truth, it is a different and wrong one. -/
theorem denote_not_fuel_monotone :
    (denote 2 tWitness).e (.str "A") = some (.s "A")
    ∧ (denote 3 tWitness).e (.str "A") = none := by
  constructor <;>
    simp [denote, tWitness, specOf, optionSemOf, altCodec, OptionSem.byAttempt,
          literalSCodec, stringCodec, Codec.empty]

/-- The honest reading of `denote_not_fuel_monotone`: at fuel `3` the union is simply
    the ill-formed one §4 already refuted — both options admit `"A"`, so (U) fails and
    the semantics returns `none`, as designed. Fuel `2` hid that by not looking. The
    defect is therefore not that `denote` is wrong at fuel `3`; it is that no monotone
    approximation to it exists, because (U) is a property of the whole option list. -/
theorem tWitness_violates_uniqueAdmission :
    ((denote 3 tWitness).e (.str "A")).isNone := by
  simp [denote_not_fuel_monotone.2]

end Calculus
