import Calculus.Soundness

/-!
# Admission lemmas shared by the exactness proofs

`refine`'s read-side gate, which `AdmA` reads, the member guard on an option's read, and a
premise checked at two options.
-/

namespace Calculus

/-- **`refine`'s read-side gate**: decode with the base, then apply `q` to what comes out.

    The row this replaces was `admA (.refine t q) = admA t` — the predicate dropped — and
    the reason on record was that `q` tests the value a read *produces*, so no *syntactic*
    set of attributes bounds it. The premise is true and the conclusion does not follow, in
    exactly the way `number`'s and `opaq`'s `⊤`s did not follow: a row is not confined to
    syntax. It may call the denotation, and the denotation is what produces the value `q`
    tests. `(denote t).p a` is that value, or `none`; the gate is `q` of it.

    `AdmA`'s `refine` row is this function, which is why the row survived the retirement of
    the per-aspect tables it was first written for. -/
noncomputable def refineReads (t : Term) (q : Value → Bool) (a : Attr) : Bool :=
  match (denote t).p a with
  | some v => q v
  | none => false

/-- The gate, unfolded at a successful read. -/
theorem refineReads_some {t : Term} {q : Value → Bool} {a : Attr} {v : Value}
    (h : (denote t).p a = some v) : refineReads t q a = q v := by
  simp [refineReads, h]

/-- …and at a failed one. -/
theorem refineReads_none {t : Term} {q : Value → Bool} {a : Attr}
    (h : (denote t).p a = none) : refineReads t q a = false := by
  simp [refineReads, h]


/-! ## Admission is guarded -/


/-- Any option's attribute admission is member-guarded: with a lawful pair and a
    named member, an admitted attribute carries that member — §5's read-side (W). -/
theorem admitA_member (t : Term) {μ a}
    (hμ : μSyn t = some μ) (hlaw : Lawful (denote t))
    (h : ((denote t).p a).isSome = true) :
    a.member = μ := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
  refine hlaw.reads ?_ hv
  rw [denote_μ]
  exact hμ

/-! ## A premise at two options -/

/-- A premise of the form `∀ t ∈ [x, y], P t`, checked at the two options. -/
theorem forall_mem_pair {α : Type} {P : α → Prop} {x y : α} (hx : P x) (hy : P y) :
    ∀ z ∈ [x, y], P z := by
  intro z hz
  rcases List.mem_cons.mp hz with rfl | hz
  · exact hx
  · rcases List.mem_cons.mp hz with rfl | hz
    · exact hy
    · exact absurd hz (by simp)

end Calculus
