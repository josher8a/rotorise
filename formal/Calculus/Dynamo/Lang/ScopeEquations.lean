import Calculus.Dynamo.Lang.Scope
import Calculus.Alg.Relations

/-!
# Equations, over the terms of a scope

The rows of `≡` that read a term, stated over the codec of a scope term at DynamoDB. Each row holds
at every table and at every environment. The inner term and the outer term of a
`held` sit below a wall, so the codec reads them at the empty environment. A `held` at the side
`false` is `through`, restricted by the write domain of the outer (`held1_host`). A `refine` is
`restrict` of the meaning of its data predicate.
-/

namespace Calculus

namespace Scoped

variable {w k : Nat} (τ : (s : Bool) → Alg.TableAt dynSig s)

/-- A `held` at the side `false` is `through`, restricted by the write domain of the outer. -/
theorem interp_held (inner outer : Term 0 0) (k₀ : DynGen × Bool) (ks : List (DynGen × Bool))
    (ρw : Fin w → Codec) (ρk : Fin k → Codec) :
    Alg.SFlat.interp (Alg.Scoped.TStep τ)
        (Term.held false inner outer k₀ ks : Term w k) ρw ρk =
      ((Alg.SFlat.interp (Alg.Scoped.TStep τ) inner Fin.elim0 Fin.elim0).through
          ((τ false).word (k₀ :: ks)).1 ((τ false).word (k₀ :: ks)).2).restrict
        fun v => ((Alg.SFlat.interp (Alg.Scoped.TStep τ) outer Fin.elim0
          Fin.elim0).e v).isSome :=
  Alg.held1_host _ _ _

/-- A `refine` is `restrict` of the meaning of its data predicate. -/
theorem interp_refine (t : Term w k) (p : Pred) (ρw : Fin w → Codec) (ρk : Fin k → Codec) :
    Alg.SFlat.interp (Alg.Scoped.TStep τ) (Term.refine t p ()) ρw ρk =
      (Alg.SFlat.interp (Alg.Scoped.TStep τ) t ρw ρk).restrict p.eval :=
  rfl

/-- The rule `(opt)`: an optional slot names the member of its term. -/
theorem optional_μ (t : Term w k) (ρw : Fin w → Codec) (ρk : Fin k → Codec) :
    (Alg.Scoped.mkField (B := dynSig) .opt
        (Alg.SFlat.interp (Alg.Scoped.TStep τ) t ρw ρk)).codec.μ =
      (Alg.SFlat.interp (Alg.Scoped.TStep τ) t ρw ρk).μ :=
  rfl

/-- `held(held(c, P, k), P′, k′) ≡ refine(held(c, P′, k ++ k′), P ∘ f′)`, over a scope term. -/
theorem equiv_held_comp (t P P' : Term 0 0) (k₀ k₀' : DynGen × Bool)
    (ks ks' : List (DynGen × Bool)) (ρw : Fin w → Codec) (ρk : Fin k → Codec) :
    Codec.Equiv
      (Alg.SFlat.interp (Alg.Scoped.TStep τ)
        (Term.held false (Term.held false t P k₀ ks) P' k₀' ks' : Term w k) ρw ρk)
      (Alg.SFlat.interp (Alg.Scoped.TStep τ)
        (Term.refine (Term.held false t P' k₀ (ks ++ k₀' :: ks'))
          (.closure fun v => ((Alg.SFlat.interp (Alg.Scoped.TStep τ) P Fin.elim0
            Fin.elim0).e (((τ false).word (k₀' :: ks')).1 v)).isSome) () : Term w k) ρw ρk) := by
  rw [interp_refine, interp_held, interp_held, interp_held]
  rw [← List.cons_append, Alg.TableAt.word_append]
  refine ⟨fun _ => ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨h1, h3⟩, h2⟩, fun ⟨⟨h1, h3⟩, h2⟩ => ⟨⟨h1, h2⟩, h3⟩⟩,
    rfl, ?_, ?_⟩
  · intro v a a' h h'
    have hl := (Alg.refine2_f.mp (Alg.through_e.mp (Alg.refine2_f.mp h).2.1)).2.1
    have hr := (Alg.refine2_f.mp (Alg.refine2_f.mp h').2.1).2.1
    exact Option.some.inj ((Alg.through_e.mp hl).symm.trans hr)
  · intro a v v' h h'
    obtain ⟨w, hw, rfl⟩ := Alg.through_p.mp (Alg.refine2_f.mp h).2.1
    obtain ⟨x, hx, rfl⟩ := Alg.through_p.mp (Alg.refine2_f.mp hw).2.1
    obtain ⟨y, hy, rfl⟩ := Alg.through_p.mp (Alg.refine2_f.mp (Alg.refine2_f.mp h').2.1).2.1
    rw [hx] at hy
    cases hy
    rfl

/-- `refine(refine(c, q), q′) ≡ refine(c, q ∩ q′)`, over a scope term. -/
theorem equiv_refine_meet (t : Term w k) (p p' : Pred) (ρw : Fin w → Codec)
    (ρk : Fin k → Codec) :
    Codec.Equiv
      (Alg.SFlat.interp (Alg.Scoped.TStep τ)
        (Term.refine (Term.refine t p ()) p' ()) ρw ρk)
      (Alg.SFlat.interp (Alg.Scoped.TStep τ)
        (Term.refine t (.closure fun v => p.eval v && p'.eval v) ()) ρw ρk) :=
  Alg.equiv_restrict_meet _ _ _

/-- `refine(c, T) ≡ c` where the predicate is the held set of the scope term. -/
theorem equiv_refine_full (t : Term w k) (p : Pred) (ρw : Fin w → Codec) (ρk : Fin k → Codec)
    (hq : ∀ v, (Alg.SFlat.interp (Alg.Scoped.TStep τ) t ρw ρk).T v ↔
      p.eval v = true) :
    Codec.Equiv
      (Alg.SFlat.interp (Alg.Scoped.TStep τ) (Term.refine t p ()) ρw ρk)
      (Alg.SFlat.interp (Alg.Scoped.TStep τ) t ρw ρk) :=
  Alg.equiv_restrict_full _ _ hq

/-- `μ(held(c)) = μ(c)` over a scope term: the inner term names the member. -/
theorem held_μ (t P : Term 0 0) (k₀ : DynGen × Bool) (ks : List (DynGen × Bool))
    (ρw : Fin w → Codec) (ρk : Fin k → Codec) :
    (Alg.SFlat.interp (Alg.Scoped.TStep τ)
        (Term.held false t P k₀ ks : Term w k) ρw ρk).μ =
      (Alg.SFlat.interp (Alg.Scoped.TStep τ) t Fin.elim0 Fin.elim0).μ :=
  rfl

/-- `μ(refine(c)) = μ(c)` over a scope term. -/
theorem refine_μ (t : Term w k) (p : Pred) (ρw : Fin w → Codec) (ρk : Fin k → Codec) :
    (Alg.SFlat.interp (Alg.Scoped.TStep τ) (Term.refine t p ()) ρw ρk).μ =
      (Alg.SFlat.interp (Alg.Scoped.TStep τ) t ρw ρk).μ :=
  rfl

end Scoped

end Calculus
