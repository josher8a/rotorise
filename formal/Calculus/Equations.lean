import Calculus.Soundness

/-!
# §6 — Equations

Which rewrites preserve the pair. `≡` is §6's own reading: the same held set, the same
member, and `e` and `p` agreeing everywhere both are defined.

All eleven of §6's "Hold" rows are proved here. Two of them are cited elsewhere as
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

The last row, `union` associativity, is the table's only *conditional* one — and it turns
out not to need its conditions. See the section below for why, and
`Refutations.not_eq_altCodec_assoc` for the behavioural difference `≡` is blind to.

The "Do not hold" table is settled in `Refutations.lean`. §6 is complete.
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

/-! ## `union` is associative

§6's last row, and the only conditional one in the table: "associative, where both sides
satisfy (D) and (K) — and only on inputs satisfying (U): an ambiguity *inside* the nested
option fails locally on the left, where the outer union may still resolve, and globally on
the right."

The behaviour is exactly as described. What the mechanization adds is that under §6's own
`≡` the conditions are **not needed** — the row holds outright. The reason is the clause
`≡` is defined with: `e` and `p` agree *where both are defined*. In precisely the case the
hedge describes the right side is undefined, so the obligation is vacuous and the two sides
cannot disagree.

That cuts both ways, and both halves are on the record: the row is stronger than §6 claims,
and `≡` is weaker than the hedge's prose suggests. `Refutations.not_eq_altCodec_assoc`
exhibits the difference `≡` cannot see. -/

/-- The member index nests the same way it flattens. Both sides conclude the head member
    or `⊤`, so the content is entirely in whether the condition agrees. -/
theorem unanimous_pair_assoc (a b c : Option Member) :
    unanimous [a, unanimous [b, c]] = unanimous [a, b, c] := by
  show (if ([unanimous [b, c]].all (· == a)) = true then a else none)
      = (if ([b, c].all (· == a)) = true then a else none)
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  by_cases hcb : (c == b) = true
  · have hu : unanimous [b, c] = b := by
      show (if ([c].all (· == b)) = true then b else none) = b
      simp only [List.all_cons, List.all_nil, Bool.and_true, if_pos hcb]
    rw [hu, eq_of_beq hcb, Bool.and_self]
  · have hu : unanimous [b, c] = none := by
      show (if ([c].all (· == b)) = true then b else none) = none
      simp only [List.all_cons, List.all_nil, Bool.and_true, if_neg hcb]
    rw [hu]
    cases a with
    | none => simp
    | some x =>
      have hne : ((b == some x) && (c == some x)) = false := by
        cases hbx : (b == some x) with
        | false => simp
        | true =>
          cases hcx : (c == some x) with
          | false => simp
          | true =>
            exact absurd (by rw [eq_of_beq hbx, eq_of_beq hcx]; simp) hcb
      simp [hne]

/-! ### Resolution, named

`altCodec` reads its option list only through "exactly one admits", so at two and three
options its pair has a small closed form. Naming those forms is what lets the
associativity argument be stated about *resolution* rather than about codecs. -/

/-- Resolving two options: the one that admits, or nothing. -/
def resolve₂ {β : Type} (B C : Bool) (E₂ E₃ : Option β) : Option β :=
  match B, C with
  | true, false => E₂
  | false, true => E₃
  | _, _ => none

/-- Resolving a *nested* union: the inner pair resolves first, and the head is consulted
    only where the inner failed. This asymmetry is the whole of §6's hedge. -/
def resolveNested {β : Type} (A : Bool) (inner E₁ : Option β) : Option β :=
  match A, inner with
  | true, none => E₁
  | false, some b => some b
  | _, _ => none

/-- Resolving three options *flat*: all three compete at once. -/
def resolve₃ {β : Type} (A B C : Bool) (E₁ E₂ E₃ : Option β) : Option β :=
  match A, B, C with
  | true, false, false => E₁
  | false, true, false => E₂
  | false, false, true => E₃
  | _, _, _ => none

theorem altCodec_pair_e (o₂ o₃ : OptionSem) (μ' : Option Member) (v : Value) :
    (altCodec [o₂, o₃] μ').e v =
      resolve₂ (o₂.admitV v) (o₃.admitV v) (o₂.c.e v) (o₃.c.e v) := by
  cases hB : o₂.admitV v <;> cases hC : o₃.admitV v <;>
    simp [altCodec, List.filter, resolve₂, hB, hC]

theorem altCodec_pair_p (o₂ o₃ : OptionSem) (μ' : Option Member) (a : Attr) :
    (altCodec [o₂, o₃] μ').p a =
      resolve₂ (o₂.admitA a) (o₃.admitA a) (o₂.c.p a) (o₃.c.p a) := by
  cases hB : o₂.admitA a <;> cases hC : o₃.admitA a <;>
    simp [altCodec, List.filter, resolve₂, hB, hC]

theorem altCodec_triple_e (o₁ o₂ o₃ : OptionSem) (μ : Option Member) (v : Value) :
    (altCodec [o₁, o₂, o₃] μ).e v =
      resolve₃ (o₁.admitV v) (o₂.admitV v) (o₃.admitV v)
        (o₁.c.e v) (o₂.c.e v) (o₃.c.e v) := by
  cases hA : o₁.admitV v <;> cases hB : o₂.admitV v <;> cases hC : o₃.admitV v <;>
    simp [altCodec, List.filter, resolve₃, hA, hB, hC]

theorem altCodec_triple_p (o₁ o₂ o₃ : OptionSem) (μ : Option Member) (a : Attr) :
    (altCodec [o₁, o₂, o₃] μ).p a =
      resolve₃ (o₁.admitA a) (o₂.admitA a) (o₃.admitA a)
        (o₁.c.p a) (o₂.c.p a) (o₃.c.p a) := by
  cases hA : o₁.admitA a <;> cases hB : o₂.admitA a <;> cases hC : o₃.admitA a <;>
    simp [altCodec, List.filter, resolve₃, hA, hB, hC]

theorem altCodec_nest_e (o₁ o₂ o₃ : OptionSem) (μ μ' : Option Member) (v : Value) :
    (altCodec [o₁, .byAttempt (altCodec [o₂, o₃] μ')] μ).e v =
      resolveNested (o₁.admitV v) ((altCodec [o₂, o₃] μ').e v) (o₁.c.e v) := by
  have key : (OptionSem.byAttempt (altCodec [o₂, o₃] μ')).admitV v
      = ((altCodec [o₂, o₃] μ').e v).isSome := rfl
  have hc : (OptionSem.byAttempt (altCodec [o₂, o₃] μ')).c = altCodec [o₂, o₃] μ' := rfl
  show (match [o₁, OptionSem.byAttempt (altCodec [o₂, o₃] μ')].filter (·.admitV v) with
        | [o] => o.c.e v | _ => none) = _
  cases hA : o₁.admitV v <;> cases hI : (altCodec [o₂, o₃] μ').e v <;>
    simp only [List.filter, hA, key, hI, hc, Option.isSome, resolveNested]

theorem altCodec_nest_p (o₁ o₂ o₃ : OptionSem) (μ μ' : Option Member) (a : Attr) :
    (altCodec [o₁, .byAttempt (altCodec [o₂, o₃] μ')] μ).p a =
      resolveNested (o₁.admitA a) ((altCodec [o₂, o₃] μ').p a) (o₁.c.p a) := by
  have key : (OptionSem.byAttempt (altCodec [o₂, o₃] μ')).admitA a
      = ((altCodec [o₂, o₃] μ').p a).isSome := rfl
  have hc : (OptionSem.byAttempt (altCodec [o₂, o₃] μ')).c = altCodec [o₂, o₃] μ' := rfl
  show (match [o₁, OptionSem.byAttempt (altCodec [o₂, o₃] μ')].filter (·.admitA a) with
        | [o] => o.c.p a | _ => none) = _
  cases hA : o₁.admitA a <;> cases hI : (altCodec [o₂, o₃] μ').p a <;>
    simp only [List.filter, hA, key, hI, hc, Option.isSome, resolveNested]

/-- The held sets coincide. Nesting a union changes how it *resolves*, never what it
    holds — which is why this half needs no side condition at all. -/
theorem altCodec_assoc_heldSet (o₁ o₂ o₃ : OptionSem) (μa μb : Option Member) (v : Value) :
    (altCodec [o₁, .byAttempt (altCodec [o₂, o₃] μb)] μa).T v
      ↔ (altCodec [o₁, o₂, o₃] μa).T v := by
  constructor
  · rintro ⟨x, hx, hT⟩
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ⟨x, List.mem_cons_self _ _, hT⟩
    · rcases List.mem_cons.mp hx' with rfl | hx''
      · obtain ⟨y, hy, hTy⟩ := hT
        exact ⟨y, List.mem_cons_of_mem _ hy, hTy⟩
      · exact absurd hx'' (by simp)
  · rintro ⟨x, hx, hT⟩
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ⟨x, List.mem_cons_self _ _, hT⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self _ _), ⟨x, hx', hT⟩⟩

/-- **Associativity, with the codecs abstracted away.** Three admission flags, three
    per-option results, and the two ways of resolving them. Whenever both resolve, they
    resolve alike.

    Reading down the eight cases — `A`, `B`, `C` being which option admits — is reading
    §6's hedge:

    * `f f f`, `f t t` — neither side resolves; the inner pair is empty or ambiguous.
    * `f f t`, `f t f`, `t f f` — exactly one option admits; both sides return it.
    * `t f t`, `t t f` — the head and one inner option both claim it; both sides refuse.
    * `t t t` — **§6's row.** The head admits and the inner pair is ambiguous, so the
      nested form's inner union fails and its outer union resolves to the head, while the
      flat form sees three claimants and refuses. One side defined, the other not, which
      is exactly why `≡` cannot see the difference and why the row needs no conditions.
      `Refutations.not_eq_altCodec_assoc` exhibits it concretely. -/
theorem nest_flat_resolve {β : Type} (A B C : Bool) (E₁ E₂ E₃ : Option β) {x y : β}
    (hn : resolveNested A (resolve₂ B C E₂ E₃) E₁ = some x)
    (hf : resolve₃ A B C E₁ E₂ E₃ = some y) : x = y := by
  cases A <;> cases B <;> cases C
  · exact nomatch hn
  · cases E₃ with
    | none => exact nomatch hn
    | some b => exact (Option.some.inj hn).symm.trans (Option.some.inj hf)
  · cases E₂ with
    | none => exact nomatch hn
    | some b => exact (Option.some.inj hn).symm.trans (Option.some.inj hf)
  · exact nomatch hn
  · exact Option.some.inj (hn.symm.trans hf)
  · cases E₃ with
    | none => exact nomatch hf
    | some b => exact nomatch hn
  · cases E₂ with
    | none => exact nomatch hf
    | some b => exact nomatch hn
  · exact nomatch hf

/-- §6: `union(c₁, union(c₂, c₃)) ≡ union(c₁, c₂, c₃)` — with no side condition.

    Each half is three steps: put both sides in closed form, then appeal to
    `nest_flat_resolve`. The write and read halves differ only in `e` versus `p`. -/
theorem equiv_altCodec_assoc (o₁ o₂ o₃ : OptionSem) :
    Codec.Equiv
      (altCodec [o₁, .byAttempt (altCodec [o₂, o₃] (unanimous [o₂.c.μ, o₃.c.μ]))]
        (unanimous [o₁.c.μ, unanimous [o₂.c.μ, o₃.c.μ]]))
      (altCodec [o₁, o₂, o₃] (unanimous [o₁.c.μ, o₂.c.μ, o₃.c.μ])) := by
  refine ⟨altCodec_assoc_heldSet o₁ o₂ o₃ _ _, unanimous_pair_assoc _ _ _, ?_, ?_⟩
  · intro v a a' hn hf
    rw [altCodec_nest_e, altCodec_pair_e] at hn
    rw [altCodec_triple_e] at hf
    exact nest_flat_resolve (o₁.admitV v) (o₂.admitV v) (o₃.admitV v)
      (o₁.c.e v) (o₂.c.e v) (o₃.c.e v) hn hf
  · intro a v v' hn hf
    rw [altCodec_nest_p, altCodec_pair_p] at hn
    rw [altCodec_triple_p] at hf
    exact nest_flat_resolve (o₁.admitA a) (o₂.admitA a) (o₃.admitA a)
      (o₁.c.p a) (o₂.c.p a) (o₃.c.p a) hn hf

end Calculus
