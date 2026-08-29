import Calculus.Soundness

/-!
# §6 — Equations

Which rewrites preserve the pair. `≡` is §6's own reading: the same held set, the same
member, and `e` and `p` agreeing everywhere both are defined.

Two rows of §6's "Hold" table are cited elsewhere as load-bearing, and those are the ones
proved here:

* `nullable(nullable(c)) ≡ nullable(c)` — §6 gives the reason the proof uses, that the
  value language has one null, and the model bears it out in the strongest form: `e` and
  `p` are *equal* on the nose, not merely agreeing. §3's separate point stands
  unchanged — null-honesty is what makes each `nullable` lawful, and so what makes the
  idempotence lawful rather than lucky; it is just not what the rewrite itself needs.
* `union(c₁ … cₙ) ≡ union(c_σ(1) … c_σ(n))` — §5 leans on this for "declaration order is
  never consulted". Proved in its generating case, the adjacent transposition, since
  those generate every permutation.

The "Do not hold" table is settled in `Refutations.lean`; the rest of the "Hold" table is not
yet mechanized (README).
-/

namespace Calculus

/-- §6's `≡`. Note it is *not* equality of the pair: `e` and `p` need only agree where
    both are defined, which is what lets a rewrite shrink a domain. -/
structure Codec.Equiv (c d : Codec) : Prop where
  /-- The same held set. -/
  heldSet : ∀ v, c.T v ↔ d.T v
  /-- The same member. -/
  member : c.μ = d.μ
  /-- `e` agrees wherever both are defined. -/
  writes : ∀ {v a a'}, c.e v = some a → d.e v = some a' → a = a'
  /-- `p` agrees wherever both are defined. -/
  reads : ∀ {a v v'}, c.p a = some v → d.p a = some v' → v = v'

theorem Codec.Equiv.refl (c : Codec) : Codec.Equiv c c :=
  ⟨fun _ => Iff.rfl, rfl, fun h h' => Option.some.inj (h.symm.trans h'),
    fun h h' => Option.some.inj (h.symm.trans h')⟩

theorem Codec.Equiv.symm {c d : Codec} (h : Codec.Equiv c d) : Codec.Equiv d c :=
  ⟨fun v => (h.heldSet v).symm, h.member.symm,
    fun hd hc => (h.writes hc hd).symm, fun hd hc => (h.reads hc hd).symm⟩

/-! ## `nullable` is idempotent -/

/-- The two pairs are not merely `≡` but equal, on both halves: the value language has
    one null, so the outer `𝟙` is the only one anything is ever written to or read
    from. -/
theorem orNull_e_idem (c : Codec) : c.orNull.orNull.e = c.orNull.e := by
  funext v
  cases v <;> rfl

theorem orNull_p_idem (c : Codec) : c.orNull.orNull.p = c.orNull.p := by
  funext a
  cases a <;> rfl

/-- §6: `nullable(nullable(c)) ≡ nullable(c)`. -/
theorem equiv_orNull_idem (c : Codec) : Codec.Equiv c.orNull.orNull c.orNull := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · intro v
    constructor
    · rintro (h | h)
      · exact h
      · exact Or.inr h
    · exact Or.inl
  · intro v a a' h h'
    rw [orNull_e_idem] at h
    exact Option.some.inj (h.symm.trans h')
  · intro a v v' h h'
    rw [orNull_p_idem] at h
    exact Option.some.inj (h.symm.trans h')

/-! ## `union` is commutative

    Resolution is unique admission, never declaration order (§5) — so swapping two
    options changes nothing. Proved for an adjacent swap, which generates every
    permutation. -/

/-- The filter of a swapped pair is the swap of the filter, and in the one case that
    matters — a singleton, where `altCodec` acts — the two are equal. -/
theorem filter_swap_singleton {α : Type} (P : α → Bool) (x y : α) (l : List α) :
    ∀ {o}, (x :: y :: l).filter P = [o] → (y :: x :: l).filter P = [o] := by
  intro o h
  cases hx : P x <;> cases hy : P y <;> simp only [List.filter, hx, hy] at h ⊢
  · exact h
  · exact h
  · exact h
  · exact nomatch h

/-- §6: `union(c₁, c₂, …) ≡ union(c₂, c₁, …)`. The pair is literally the same on every
    input at which either side is defined, since `altCodec` reads the option list only
    through "exactly one admits". -/
theorem equiv_altCodec_swap (o₁ o₂ : OptionSem) (os : List OptionSem)
    (μA : Option Member) :
    Codec.Equiv (altCodec (o₁ :: o₂ :: os) μA) (altCodec (o₂ :: o₁ :: os) μA) := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · intro v
    constructor <;> rintro ⟨o, ho, hT⟩ <;>
      · rcases List.mem_cons.mp ho with rfl | ho'
        · exact ⟨o, List.mem_cons_of_mem _ (List.mem_cons_self _ _), hT⟩
        · rcases List.mem_cons.mp ho' with rfl | ho''
          · exact ⟨o, List.mem_cons_self _ _, hT⟩
          · exact ⟨o, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ho''), hT⟩
  · intro v a a' h h'
    replace h : (match (o₁ :: o₂ :: os).filter (·.admitV v) with
      | [o] => o.c.e v | _ => none) = some a := h
    cases hf : (o₁ :: o₂ :: os).filter (·.admitV v) with
    | nil => rw [hf] at h; exact nomatch h
    | cons o tl =>
      cases tl with
      | cons _ _ => rw [hf] at h; exact nomatch h
      | nil =>
        rw [hf] at h
        replace h' : (match (o₂ :: o₁ :: os).filter (·.admitV v) with
          | [o] => o.c.e v | _ => none) = some a' := h'
        rw [filter_swap_singleton _ _ _ _ hf] at h'
        exact Option.some.inj (h.symm.trans h')
  · intro a v v' h h'
    replace h : (match (o₁ :: o₂ :: os).filter (·.admitA a) with
      | [o] => o.c.p a | _ => none) = some v := h
    cases hf : (o₁ :: o₂ :: os).filter (·.admitA a) with
    | nil => rw [hf] at h; exact nomatch h
    | cons o tl =>
      cases tl with
      | cons _ _ => rw [hf] at h; exact nomatch h
      | nil =>
        rw [hf] at h
        replace h' : (match (o₂ :: o₁ :: os).filter (·.admitA a) with
          | [o] => o.c.p a | _ => none) = some v' := h'
        rw [filter_swap_singleton _ _ _ _ hf] at h'
        exact Option.some.inj (h.symm.trans h')

end Calculus
