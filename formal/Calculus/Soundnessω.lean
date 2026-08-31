import Calculus.Denoteω
import Calculus.Soundness

/-!
# The ω-restatement was the statement

This file restated §5's theorem on `denoteω` by transporting each fueled result along
`denoteω_eq` at `termDepth t` — the fuel that "covered" the term. With `denote` fuel-free and
`denoteω` a name for it, every one of those transports is the identity, and `Obligationsω`,
which was `Obligations (termDepth t) t`, is `Obligations t`.

So the ω-names remain as aliases and the theorems are the theorems. What this file *was* — 77
lines of transport — is what the fuel cost.
-/

namespace Calculus

noncomputable section

/-- `Obligations`, under the name the ω-results use. It was `Obligations (termDepth t) t`. -/
@[reducible] def Obligationsω : Term → Prop := Obligations

/-- …and likewise. -/
@[reducible] def MPOkω : Term → Prop := MPOk

/-- The transport, now `rfl`: there are not two denotations to relate. -/
theorem denoteω_self (t : Term) : denoteω t = denote t := rfl

/-- §5 Theorem (soundness), core half: (R), (C), (W) for every derivable term, `legacy`
    included. -/
theorem soundness_coreω {t T μ} (h : Typed t T μ) (hob : Obligationsω t) :
    LawfulCore (denoteω t) := soundness_core h hob

/-- §5 Theorem (soundness), full: all four laws where the derivation is legacy-free. -/
theorem soundnessω {t T μ} (h : Typed t T μ) (hob : Obligationsω t) (hmp : MPOkω t) :
    Lawful (denoteω t) := soundness h hob hmp

/-- The pair is on its carrier — §3's `e : T ⇀ 𝔸` and `p : 𝔸 ⇀ T`. -/
theorem carrier_denoteω {t T μ} (h : Typed t T μ) (hob : Obligationsω t) :
    Carrier (denoteω t) := carrier_denote h hob

/-- §3's `e : T ⇀ 𝔸` at the judgement's own index. -/
theorem typed_e_memω {t T μ} (h : Typed t T μ) (hob : Obligationsω t)
    {v a} (he : (denoteω t).e v = some a) : T v := typed_e_mem h hob he

/-- §3's `p : 𝔸 ⇀ T` at the judgement's own index. -/
theorem typed_p_memω {t T μ} (h : Typed t T μ) (hob : Obligationsω t)
    {a v} (hp : (denoteω t).p a = some v) : T v := typed_p_mem h hob hp

/-- The `⇝` index is the member the denotation actually stores. -/
theorem typed_μSynω {t T μ} (h : Typed t T μ) : (denoteω t).μ = μ := by
  rw [denoteω_μ t]; exact typed_μSyn h

end

end Calculus
