import Calculus.Dynamo.Alg.Prisms
import Calculus.Dynamo.Alg.Frontier

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

/-! ## The witnesses -/

/-- The stable option: `literal("A")`, which admits `"A"` at every stage. -/
noncomputable def optLit : Codec := (literalCodec .string "A")

/-! ### The obligation is not free, and a new witness is needed -/

/-- A pair that writes `⟨S,"B"⟩` where the literal writes `⟨S,"A"⟩`. -/
def ceBad : Value → Option Attr :=
  fun v => match v with | .str "A" => some (.s "B") | _ => none

/-- …as a codec, and `Codec.empty` approximates it, so the growth is legitimate. -/
def cBad : Codec :=
  Alg.Codec.ofEP (T := fun v => (ceBad v).isSome) (μ := none) (e := ceBad) (p := fun _ => none)

/-- …as an option. -/
def optBad : Codec := cBad

/-- **The counterexample the obligation excludes**: with the growing option first, the answer
    **changes**, `⟨S,"A"⟩` to `⟨S,"B"⟩`. -/
theorem selectF_not_monotone :
    selectF [optBot, optLit] (.str "A") = some (.s "A")
    ∧ selectF [optBad, optLit] (.str "A") = some (.s "B") := by
  constructor <;>
    simp [selectF, select, optBot, optBad, optLit, cBad, ceBad, Codec.empty, literalCodec, baseCodec, Alg.restrict_e_def, Alg.restrict_p_def, inL, prism_rows, Alg.Codec.e, Alg.Codec.p]

/-- …and the obligation is exactly what that violates. -/
theorem optBad_not_confluent : ¬ ConfluentAt [optBad, optLit] (.str "A") := by
  intro h
  have := h optBad (by simp) optLit (by simp)
    (by simp [optBad, cBad, ceBad])
    (by simp [optLit, literalCodec, baseCodec, Alg.restrict_e_def, Alg.restrict_p_def, inL, prism_rows, Alg.Codec.e, Alg.Codec.p])
  simp [optBad, optLit, cBad, ceBad, literalCodec, baseCodec, Alg.restrict_e_def, Alg.restrict_p_def, inL, prism_rows, Alg.Codec.e, Alg.Codec.p] at this

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
