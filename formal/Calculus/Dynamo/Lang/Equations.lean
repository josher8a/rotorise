import Calculus.Dynamo.Lang.Denote
import Calculus.Dynamo.Alg.Opaque

variable {α : Calculus.Table}

/-!
# Equations

Which rewrites preserve the pair. `≡` reads as: the same held set, the same
member, and `e` and `p` agreeing everywhere both are defined.

The rows of `≡` that read only the combinators take the carriers as parameters, as `Codec.Equiv`
does. This file states the rows that read a term, a field, or the member of a union. Two of the
rows are cited elsewhere as load-bearing and came first:

* `union(c₁ … cₙ) ≡ union(c_σ(1) … c_σ(n))` — the admission leans on this for "declaration order is
  never consulted". Proved at *every* permutation and as an **equality** of the pair
  (`altCodec_perm`), not merely `≡`, over pairwise compatible, lawful options. Deriving the general case from the adjacent one would
  need `≡` to compose, and `Refutations.not_equiv_trans` says it does not.

The remaining rows: `held`'s composition, `refine`'s meet and its full case,
`alternate reader` with its own reading (and `≈` on `Can(c)`), `union` of one, and the member
preservation of the three codec wrappers. `held`'s identity is a row of the codecs
(`equiv_through_id`) and no row of the terms: a `held` with the empty word has no term.

The last row, `union` associativity, needs no condition: a nested union and its flattening
consult the same options in the same order, so the two are equal on both halves.

The "Do not hold" table is settled in `Refutations.lean`. Every row of `≡` is stated.
-/

namespace Calculus

/-! ## Wrappers preserve the member

The last "Hold" row of `≡` is `μ(w(c)) = μ(c)` for a wrapper `w`. A field carries a member like
anything else, and `FieldSem.codec` is where the model puts it, so the row at `optional` is
`rfl` through that accessor (`optional_μ`). The codec wrappers `held` and `refine` keep the
member by `rfl` as well (`denote_held_μ`, `denote_refine_μ`). -/

/-- The rule `(opt)`: an optional attribute is still stored somewhere, and where is the
    subterm's member. -/
theorem optional_μ (t : Term) : (fieldSem α (.optional t)).codec.μ = (denote α t).μ := rfl

/-! ## `union` is associative

The row of `≡`, stated outright. Both forms take the first admitter in the same order, so the
two maps are equal at each orientation (`altCodec_nest`), and the row carries no condition. -/

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

/-- `union(c₁, union(c₂, c₃)) ≡ union(c₁, c₂, c₃)` — with no side condition. -/
theorem equiv_altCodec_assoc (o₁ o₂ o₃ : Codec) :
    Codec.Equiv
      (altCodec [o₁, (altCodec [o₂, o₃] (unanimous [o₂.μ, o₃.μ]))]
        (unanimous [o₁.μ, unanimous [o₂.μ, o₃.μ]]))
      (altCodec [o₁, o₂, o₃] (unanimous [o₁.μ, o₂.μ, o₃.μ])) := by
  refine ⟨altCodec_assoc_heldSet o₁ o₂ o₃ _ _, unanimous_pair_assoc _ _ _, ?_, ?_⟩
  · intro v a a' hn hf
    exact Option.some.inj ((hn.symm.trans (altCodec_nest o₁ o₂ o₃ _ _ _ (o := .host) v)).trans hf)
  · intro a v v' hn hf
    exact Option.some.inj ((hn.symm.trans (altCodec_nest o₁ o₂ o₃ _ _ _ (o := .dual) a)).trans hf)

/-! ## The Hold rows of `≡`, at term level

Each row's twin, stated about a
`Term`, the way `Refutations.lean`'s "Do not hold" rows already are. Every one is its
combinator row through the bridge above, so they cost a line each and buy the property
the representation audit asked for — both halves of `≡` in one language. -/

section Terms

/-- `held(held(c, P, k), P′, k′) ≡ refine(held(c, P′, k ++ k′), P ∘ f′)`, where `f′` is
    the caller-side function of `k′`. The words concatenate, so the transforms compose, and the
    inner restriction pulls back along `f′`. The pullback is a predicate and no term, so the right
    side carries it as a `refine`. -/
theorem equiv_denote_held_comp (t P P' : Term) (k₀ k₀' : DynGen × Bool) (k k' : Word) :
    Codec.Equiv (denote α (.held false (.held false t P k₀ k) P' k₀' k'))
      (denote α (.refine (.held false t P' k₀ (k ++ k₀' :: k'))
        (.closure fun v => ((denote α P).e ((α.word (k₀' :: k')).1 v)).isSome) ())) := by
  simp only [denote_rows]
  rw [← List.cons_append, Alg.TableAt.word_append]
  refine ⟨fun _ => ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨h1, h3⟩, h2⟩, fun ⟨⟨h1, h3⟩, h2⟩ => ⟨⟨h1, h2⟩, h3⟩⟩,
    rfl, ?_, ?_⟩
  · intro v a a' h h'
    have hl := (Alg.refine2_f.mp (through_e.mp (Alg.refine2_f.mp h).2.1)).2.1
    have hr := (Alg.refine2_f.mp (refine2_f.mp h').2.1).2.1
    exact Option.some.inj ((through_e.mp hl).symm.trans hr)
  · intro a v v' h h'
    obtain ⟨w, hw, rfl⟩ := through_p.mp (Alg.refine2_f.mp h).2.1
    obtain ⟨x, hx, rfl⟩ := through_p.mp (Alg.refine2_f.mp hw).2.1
    obtain ⟨y, hy, rfl⟩ := through_p.mp (Alg.refine2_f.mp (refine2_f.mp h').2.1).2.1
    rw [hx] at hy
    cases hy
    rfl

/-- `refine(refine(c, q), q′) ≡ refine(c, q ∩ q′)`.

    **The meet is a `closure`, and that is what `Pred` costs.** The equation is about codecs
    and it holds: `equiv_restrict_meet` applies, because `restrict` takes a
    `Value → Bool` and `denote` hands it `p.eval`. What the reified predicate cannot do is
    keep the *shape*.

    For the reader who reaches for a fourth constructor: two `members` at one base meet in a
    `members` over the intersection, where the intersection is nonempty. A discharger that
    needs that reduction states it as a lemma about `Pred`, and `Pred` stays one to one with
    the host's three cases, which is the whole reason it has three. -/
theorem equiv_denote_refine_meet (t : Term) (p p' : Pred) :
    Codec.Equiv (denote α (.refine (.refine t p ()) p' ()))
      (denote α (.refine t (.closure (fun v => p.eval v && p'.eval v)) ())) := by
  simp only [denote_rows]
  exact equiv_restrict_meet _ _ _

/-- `refine(c, T) ≡ c` for `⊢ c : T ⇝ μ`. The premise is the row's, read off the
    denotation rather than the judgement — `typed_TSub` is what connects the two. -/
theorem equiv_denote_refine_full (t : Term) (p : Pred)
    (hq : ∀ v, (denote α t).T v ↔ p.eval v = true) :
    Codec.Equiv (denote α (.refine t p ())) (denote α t) := by
  simp only [denote_rows]
  exact equiv_restrict_full _ _ hq

/-- `μ(w(c)) = μ(c)` for the codec wrappers `held` and `refine`. The field wrapper is
    `optional_μ`, which is stated over a denotation. -/
theorem denote_held_μ (t P : Term) (k₀ : DynGen × Bool) (k : Word) :
    (denote α (.held false t P k₀ k)).μ = (denote α t).μ := rfl

theorem denote_refine_μ (t : Term) (p : Pred) :
    (denote α (.refine t p ())).μ = (denote α t).μ := rfl

end Terms

end Calculus
