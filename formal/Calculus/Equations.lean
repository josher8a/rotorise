import Calculus.Soundness

/-!
# §6 — Equations

Which rewrites preserve the pair. `≡` is §6's own reading: the same held set, the same
member, and `e` and `p` agreeing everywhere both are defined.

Ten of §6's eleven "Hold" rows are proved here. Two of them are cited elsewhere as
load-bearing and came first:

* `nullable(nullable(c)) ≡ nullable(c)` — §6 gives the reason the proof uses, that the
  value language has one null, and the model bears it out in the strongest form: `e` and
  `p` are *equal* on the nose, not merely agreeing. §3's separate point stands
  unchanged — null-honesty is what makes each `nullable` lawful, and so what makes the
  idempotence lawful rather than lucky; it is just not what the rewrite itself needs.
* `union(c₁ … cₙ) ≡ union(c_σ(1) … c_σ(n))` — §5 leans on this for "declaration order is
  never consulted". Proved in its generating case, the adjacent transposition, since
  those generate every permutation.

The remaining rows: `held`'s identity and composition, `refine`'s meet and its full case,
`legacy` with its own reading (and `≈` on `Can(c)`), `union` of one, and the member
preservation of the three codec wrappers.

One row is open — `union(c₁, union(c₂, c₃)) ≡ union(c₁, c₂, c₃)`. It is the only
*conditional* row in the table, and §6 states the condition honestly: both sides must
satisfy (D) and (K), and it holds only on inputs satisfying (U), because an ambiguity
inside the nested option fails locally on the left — where the outer union may still
resolve — and globally on the right. Refuting or proving it needs the (U) premise
threaded through both nestings; `Continuity.lean` is the reason to expect that to be
delicate rather than routine.

The "Do not hold" table is settled in `Refutations.lean`.
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

/-! ## `held` is an identity, and composes

§6's first two rows. The second is the one worth stating carefully: the writing halves
compose in the order written and the reading halves compose *reversed*, which is what
"note the reversal on the reading half" means and what the model makes literal. -/

/-- §6: `held(c, id, id) ≡ c`. -/
theorem equiv_through_id (c : Codec) : Codec.Equiv (c.through id id) c := by
  refine ⟨fun _ => Iff.rfl, rfl, ?_, ?_⟩
  · intro v a a' h h'
    exact Option.some.inj (h.symm.trans h')
  · intro a v v' h h'
    replace h : (c.p a).map id = some v := h
    cases hp : c.p a with
    | none => rw [hp] at h; exact nomatch h
    | some x =>
      rw [hp] at h
      replace h : x = v := by simpa using h
      rw [hp] at h'
      exact h.symm.trans (Option.some.inj h')

/-- §6: `held(held(c, f, g), f′, g′) ≡ held(c, f ∘ f′, g′ ∘ g)`. -/
theorem equiv_through_comp (c : Codec) (f g f' g' : Value → Value) :
    Codec.Equiv ((c.through f g).through f' g') (c.through (f ∘ f') (g' ∘ g)) := by
  refine ⟨fun _ => Iff.rfl, rfl, ?_, ?_⟩
  · intro v a a' h h'
    exact Option.some.inj (h.symm.trans h')
  · intro a v v' h h'
    replace h : ((c.p a).map g).map g' = some v := h
    replace h' : (c.p a).map (g' ∘ g) = some v' := h'
    cases hp : c.p a with
    | none => rw [hp] at h; exact nomatch h
    | some x =>
      rw [hp] at h h'
      replace h : g' (g x) = v := by simpa using h
      replace h' : g' (g x) = v' := by simpa using h'
      exact h.symm.trans h'

/-! ## `refine` — prisms meet, and a full one is no refinement -/

/-- §6: `refine(refine(c, q), q′) ≡ refine(c, q ∩ q′)`. -/
theorem equiv_restrict_meet (c : Codec) (q q' : Value → Bool) :
    Codec.Equiv ((c.restrict q).restrict q') (c.restrict (fun v => q v && q' v)) := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · intro v
    constructor
    · rintro ⟨⟨hT, hq⟩, hq'⟩
      exact ⟨hT, by simp [hq, hq']⟩
    · rintro ⟨hT, hqq⟩
      simp only [Bool.and_eq_true] at hqq
      exact ⟨⟨hT, hqq.1⟩, hqq.2⟩
  · intro v a a' h h'
    replace h : (if q' v = true then (if q v = true then c.e v else none) else none)
        = some a := h
    replace h' : (if (q v && q' v) = true then c.e v else none) = some a' := h'
    by_cases hq' : q' v = true
    · rw [if_pos hq'] at h
      by_cases hq : q v = true
      · rw [if_pos hq] at h
        rw [if_pos (by simp [hq, hq'])] at h'
        exact Option.some.inj (h.symm.trans h')
      · rw [if_neg hq] at h; exact nomatch h
    · rw [if_neg hq'] at h; exact nomatch h
  · intro a v v' h h'
    replace h : ((c.p a).bind fun x => if q x = true then some x else none).bind
        (fun x => if q' x = true then some x else none) = some v := h
    replace h' : (c.p a).bind (fun x => if (q x && q' x) = true then some x else none)
        = some v' := h'
    cases hp : c.p a with
    | none => rw [hp] at h; exact nomatch h
    | some x =>
      rw [hp] at h h'
      replace h : (if q x = true then some x else none).bind
          (fun y => if q' y = true then some y else none) = some v := h
      replace h' : (if (q x && q' x) = true then some x else none) = some v' := h'
      by_cases hq : q x = true
      · rw [if_pos hq] at h
        replace h : (if q' x = true then some x else none) = some v := h
        by_cases hq' : q' x = true
        · rw [if_pos hq'] at h
          rw [if_pos (by simp [hq, hq'])] at h'
          exact (Option.some.inj h).symm.trans (Option.some.inj h')
        · rw [if_neg hq'] at h; exact nomatch h
      · rw [if_neg hq] at h
        replace h : (none : Option Value) = some v := h
        exact nomatch h

/-- §6: `refine(c, T) ≡ c` for `⊢ c : T ⇝ μ`. A refinement admitting everything the codec
    holds is no refinement — and note the premise needed is only that `q` agrees with `T`,
    not that the pair is on its carrier: `≡` compares `e` and `p` where *both* are defined,
    so a `q` that rejects something outside `T` costs nothing. -/
theorem equiv_restrict_full (c : Codec) (q : Value → Bool)
    (hq : ∀ v, c.T v ↔ q v = true) : Codec.Equiv (c.restrict q) c := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · intro v
    exact ⟨fun h => h.1, fun h => ⟨h, (hq v).mp h⟩⟩
  · intro v a a' h h'
    replace h : (if q v = true then c.e v else none) = some a := h
    cases hqv : q v <;> simp only [hqv] at h
    · exact nomatch h
    · exact Option.some.inj (h.symm.trans h')
  · intro a v v' h h'
    replace h : (c.p a).bind (fun x => if q x = true then some x else none) = some v := h
    cases hp : c.p a with
    | none => rw [hp] at h; exact nomatch h
    | some x =>
      rw [hp] at h h'
      replace h : (if q x = true then some x else none) = some v := h
      by_cases hqx : q x = true
      · rw [if_pos hqx] at h
        exact (Option.some.inj h).symm.trans (Option.some.inj h')
      · rw [if_neg hqx] at h; exact nomatch h

/-! ## `legacy` with its own reading -/

/-- The pair is not merely `≡` but equal: both branches of `extendRead`'s match give
    `c.p a`, so re-reading through `c`'s own `p` adds nothing at all. -/
theorem extendRead_self_p (c : Codec) : (c.extendRead c.p).p = c.p := by
  funext a
  show (match c.p a with | some v => some v | none => c.p a) = c.p a
  cases c.p a <;> rfl

/-- §6: `legacy(c, p_c) ≡ c`. -/
theorem equiv_extendRead_self (c : Codec) : Codec.Equiv (c.extendRead c.p) c := by
  refine ⟨fun _ => Iff.rfl, rfl, ?_, ?_⟩
  · intro v a a' h h'
    exact Option.some.inj (h.symm.trans h')
  · intro a v v' h h'
    rw [extendRead_self_p] at h
    exact Option.some.inj (h.symm.trans h')

/-- §2's `Can(c)`: the attributes some value actually writes. §6's `≈` rows are the ones
    stated on this set rather than on all of `𝔸`. -/
def Can (c : Codec) (a : Attr) : Prop := ∃ v, c.e v = some a

/-- §6: `legacy(c, r) ≈ c` on `Can(c)`. A migration differs from the current encoding only
    *off* the canonical set — on it, `(R)` has already made `c.p` succeed, so `r` is never
    consulted. The premise is exactly `(R)`, which is why this row is about lawful codecs
    and not about `extendRead` in general. -/
theorem extendRead_eq_on_can (c : Codec) (r : Attr → Option Value) (hc : Lawful c)
    {a : Attr} (ha : Can c a) : (c.extendRead r).p a = c.p a := by
  obtain ⟨v, hv⟩ := ha
  have hp : c.p a = some v := hc.retract hv
  show (match c.p a with | some v => some v | none => r a) = c.p a
  rw [hp]

/-! ## `union` of one -/

/-- §6: `union(c) ≡ c`. Choice of one: the filter is `[o]` exactly when `o` admits, and
    `altCodec` then reads `o`'s own pair. Where `o` does not admit, the union is undefined
    and `≡` asks nothing — which is the clause that makes this row true for a `byNames`
    option as well as a `byAttempt` one. -/
theorem equiv_altCodec_single (o : OptionSem) :
    Codec.Equiv (altCodec [o] o.c.μ) o.c := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · intro v
    constructor
    · rintro ⟨x, hx, hT⟩
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hT
      · exact absurd hx' (by simp)
    · exact fun h => ⟨o, List.mem_cons_self _ _, h⟩
  · intro v a a' h h'
    replace h : (match [o].filter (·.admitV v) with | [x] => x.c.e v | _ => none)
        = some a := h
    cases hp : o.admitV v <;> simp only [List.filter, hp] at h
    · exact nomatch h
    · exact Option.some.inj (h.symm.trans h')
  · intro a v v' h h'
    replace h : (match [o].filter (·.admitA a) with | [x] => x.c.p a | _ => none)
        = some v := h
    cases hp : o.admitA a <;> simp only [List.filter, hp] at h
    · exact nomatch h
    · exact Option.some.inj (h.symm.trans h')

/-! ## Wrappers preserve the member

§6's last "Hold" row, and §4's reason index keys stay stable under refactoring: none of
`held`, `refine` or `legacy` touches `μ`. The field wrappers `optional` and `fallback` are
`FieldSem`s rather than codecs, so their half of the row is the stratification of §4 and
not a statement about `Codec.μ` at all. -/

theorem through_μ (c : Codec) (f g : Value → Value) : (c.through f g).μ = c.μ := rfl

theorem restrict_μ (c : Codec) (q : Value → Bool) : (c.restrict q).μ = c.μ := rfl

theorem extendRead_μ (c : Codec) (r : Attr → Option Value) :
    (c.extendRead r).μ = c.μ := rfl

end Calculus
