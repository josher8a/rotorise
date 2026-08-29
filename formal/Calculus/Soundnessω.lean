import Calculus.Soundness
import Calculus.Denoteω

/-!
# §5, without fuel

The theorem, restated on `denoteω`. Nothing is reproved: `denoteω_eq` makes the two
denotations *equal* at sufficient fuel, and `termDepth t` is sufficient for `t` by
construction, so every fueled statement transports.

What this buys is what `docs/codec-formalization.md` §7 asked for and could not get from a
change of proof assistant — the conclusions no longer mention fuel:

```
soundnessω : Typed t T μ → Obligationsω t → MPOkω t → Lawful (denoteω t)
```

`Obligationsω` and `MPOkω` are the doc's premises at the term's own depth. They are
*not* weaker than the fueled forms: `Obligations n t` for `n ≥ termDepth t` asks the same
questions, because past that depth `denote n t` has stopped changing.

The one statement that never needed transport is `denoteω_μ` (Denoteω.lean): the member
index was fuel-free all along (`μSyn`), which is why §3's `⇝` column was the first part of
the judgement to be honest.
-/

namespace Calculus

/-- The doc's semantic rule premises, at the term's own depth. -/
def Obligationsω (t : Term) : Prop := Obligations (termDepth t) t

/-- Legacy-free, at the term's own depth — the doc's (MP) exemption. -/
def MPOkω (t : Term) : Prop := MPOk (termDepth t) t

/-- `denoteω t` *is* the fueled denotation at the term's own depth. The bridge every
    statement below crosses. -/
theorem denoteω_self (t : Term) : denoteω t = denote (termDepth t) t :=
  denoteω_eq t (termDepth t) (Nat.le_refl _)

/-- §5 Theorem (soundness), core half, fuel-free: (R), (C), (W) for every derivable
    term, `legacy` included. -/
theorem soundness_coreω {t T μ} (h : Typed t T μ) (hob : Obligationsω t) :
    LawfulCore (denoteω t) := by
  rw [denoteω_self t]
  exact soundness_core (termDepth t) h hob

/-- §5 Theorem (soundness), full, fuel-free: all four laws where the derivation is
    legacy-free. -/
theorem soundnessω {t T μ} (h : Typed t T μ) (hob : Obligationsω t) (hmp : MPOkω t) :
    Lawful (denoteω t) := by
  rw [denoteω_self t]
  exact soundness (termDepth t) h hob hmp

/-- The pair is on its carrier — §3's `e : T ⇀ 𝔸` and `p : 𝔸 ⇀ T`. -/
theorem carrier_denoteω {t T μ} (h : Typed t T μ) (hob : Obligationsω t) :
    Carrier (denoteω t) := by
  rw [denoteω_self t]
  exact carrier_denote (termDepth t) h hob

/-- §3's `e : T ⇀ 𝔸` at the judgement's own index, fuel-free. -/
theorem typed_e_memω {t T μ} (h : Typed t T μ) (hob : Obligationsω t)
    {v a} (he : (denoteω t).e v = some a) : T v := by
  rw [denoteω_self t] at he
  exact typed_e_mem (termDepth t) h hob he

/-- §3's `p : 𝔸 ⇀ T` at the judgement's own index, fuel-free. -/
theorem typed_p_memω {t T μ} (h : Typed t T μ) (hob : Obligationsω t)
    {a v} (hp : (denoteω t).p a = some v) : T v := by
  rw [denoteω_self t] at hp
  exact typed_p_mem (termDepth t) h hob hp

/-- The `⇝` index is the member the fuel-free denotation actually stores. -/
theorem typed_μSynω {t T μ} (h : Typed t T μ) : (denoteω t).μ = μ := by
  rw [denoteω_μ t]
  exact typed_μSyn h

end Calculus
