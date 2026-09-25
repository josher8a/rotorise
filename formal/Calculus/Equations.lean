import Calculus.Soundness
import Calculus.Denote
import Calculus.Opaque

/-!
# §6 — Equations

Which rewrites preserve the pair. `≡` is §6's own reading: the same held set, the same
member, and `e` and `p` agreeing everywhere both are defined.

The rows of §6 that read only the combinators take the carriers as parameters, as `Codec.Equiv`
does. This file states the rows that read a term, a field, or the member of a union. Two of the
rows are cited elsewhere as load-bearing and came first:

* `union(c₁ … cₙ) ≡ union(c_σ(1) … c_σ(n))` — §5 leans on this for "declaration order is
  never consulted". Proved at *every* permutation and as an **equality** of the pair
  (`altCodec_perm`), not merely `≡`, over pairwise compatible, lawful options. Deriving the general case from the adjacent one would
  need `≡` to compose, and `Refutations.not_equiv_trans` says it does not.

The remaining rows: `held`'s identity and composition, `refine`'s meet and its full case,
`alternate reader` with its own reading (and `≈` on `Can(c)`), `union` of one, and the member
preservation of the three codec wrappers.

The last row, `union` associativity, needs no condition: a nested union and its flattening
consult the same options in the same order, so the two are equal on both halves.

The "Do not hold" table is settled in `Refutations.lean`. §6 is complete.
-/

namespace Calculus

/-! ## Wrappers preserve the member

§6's last "Hold" row, `μ(w(c)) = μ(c)` for `w ∈ {held, refine, legacy, optional,

Three of the five are codec wrappers. The other two are **fields**, and this file used to
say their half of the row was "the stratification of §4 and not a statement about
`Codec.μ` at all". That was an evasion: §4 says in as many words that *a field carries a
member like anything else*, and `FieldSem.codec` is where the model puts it. Stated
through that accessor the two rows are `rfl` — which is the honest form of the claim
rather than a reason to skip it, and it is what makes the row five of five. -/

/-- §4 `(opt)`: an optional attribute is still stored somewhere, and where is the
    subterm's member. -/
theorem optional_μ (t : Term) : (fieldSem (.optional t)).codec.μ = (denote t).μ := rfl

/-! ## `union` is associative

§6's row, stated outright. Both forms take the first admitter in the same order, so the
write and read halves are equal (`altCodec_nest_e`, `altCodec_nest_p`), and the row carries
no condition. -/

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

/-- §6: `union(c₁, union(c₂, c₃)) ≡ union(c₁, c₂, c₃)` — with no side condition. -/
theorem equiv_altCodec_assoc (o₁ o₂ o₃ : Codec) :
    Codec.Equiv
      (altCodec [o₁, (altCodec [o₂, o₃] (unanimous [o₂.μ, o₃.μ]))]
        (unanimous [o₁.μ, unanimous [o₂.μ, o₃.μ]]))
      (altCodec [o₁, o₂, o₃] (unanimous [o₁.μ, o₂.μ, o₃.μ])) := by
  refine ⟨altCodec_assoc_heldSet o₁ o₂ o₃ _ _, unanimous_pair_assoc _ _ _, ?_, ?_⟩
  · intro v a a' hn hf
    rw [altCodec_nest_e (μf := unanimous [o₁.μ, o₂.μ, o₃.μ])] at hn
    exact Option.some.inj (hn.symm.trans hf)
  · intro a v v' hn hf
    rw [altCodec_nest_p (μf := unanimous [o₁.μ, o₂.μ, o₃.μ])] at hn
    exact Option.some.inj (hn.symm.trans hf)

/-! ## §6's Hold rows, at term level

Each row's twin, stated where a reader of the specification's §6 would look for it: about a
`Term`, the way `Refutations.lean`'s "Do not hold" rows already are. Every one is its
combinator row through the bridge above, so they cost a line each and buy the property
the representation audit asked for — both halves of §6 in one language. -/

section Terms

/-- §6: `held(c, P, id, id) ≡ refine(c, P)`. The identity transform leaves the caller-side
    restriction, and that restriction is a `refine` by the admission of `P`. -/
theorem equiv_denote_held_id (t P : Term) :
    Codec.Equiv (denote (.held t P id id))
      (denote (.refine t (.closure fun v => ((denote P).e v).isSome))) := by
  refine ⟨fun _ => Iff.rfl, rfl, ?_, ?_⟩
  · intro v a a' h h'
    exact Option.some.inj ((through_e.mp (restrict_e.mp h).2).symm.trans (restrict_e.mp h').2)
  · intro a v v' h h'
    obtain ⟨w, hw, rfl⟩ := through_p.mp (restrict_p.mp h).1
    exact Option.some.inj (hw.symm.trans (restrict_p.mp h').1)

/-- §6: `held(held(c, P, f, g), P′, f′, g′) ≡ refine(held(c, P′, f ∘ f′, g′ ∘ g), P ∘ f′)`.
    The transforms compose, and the inner caller-side restriction pulls back along `f′`. The
    pullback is a predicate and no term, so the right side carries it as a `refine`. -/
theorem equiv_denote_held_comp (t P P' : Term) (f g f' g' : Value → Value) :
    Codec.Equiv (denote (.held (.held t P f g) P' f' g'))
      (denote (.refine (.held t P' (f ∘ f') (g' ∘ g))
        (.closure fun v => ((denote P).e (f' v)).isSome))) := by
  refine ⟨fun _ => ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨h1, h3⟩, h2⟩, fun ⟨⟨h1, h3⟩, h2⟩ => ⟨⟨h1, h2⟩, h3⟩⟩,
    rfl, ?_, ?_⟩
  · intro v a a' h h'
    have hl := (restrict_e.mp (through_e.mp (restrict_e.mp h).2)).2
    have hr := (restrict_e.mp (restrict_e.mp h').2).2
    exact Option.some.inj ((through_e.mp hl).symm.trans hr)
  · intro a v v' h h'
    obtain ⟨w, hw, rfl⟩ := through_p.mp (restrict_p.mp h).1
    obtain ⟨x, hx, rfl⟩ := through_p.mp (restrict_p.mp hw).1
    obtain ⟨y, hy, rfl⟩ := through_p.mp (restrict_p.mp (restrict_p.mp h').1).1
    rw [hx] at hy
    cases hy
    rfl

/-- §6: `refine(refine(c, q), q′) ≡ refine(c, q ∩ q′)`.

    **The meet is a `closure`, and that is what `Pred` costs.** The equation is about codecs
    and it holds: `equiv_restrict_meet` is unchanged, because `restrict` still takes a
    `Value → Bool` and `denote` hands it `p.eval`. What the reified predicate cannot do is
    keep the *shape*.

    For the reader who reaches for a fourth constructor: two `members` at one base meet in a
    `members` over the intersection, where the intersection is nonempty. A discharger that
    needs that reduction states it as a lemma about `Pred`, and `Pred` stays one to one with
    the host's three cases, which is the whole reason it has three. -/
theorem equiv_denote_refine_meet (t : Term) (p p' : Pred) :
    Codec.Equiv (denote (.refine (.refine t p) p'))
      (denote (.refine t (.closure (fun v => p.eval v && p'.eval v)))) :=
  equiv_restrict_meet _ _ _

/-- §6: `refine(c, T) ≡ c` for `⊢ c : T ⇝ μ`. The premise is the row's, read off the
    denotation rather than the judgement — `typed_TSub` is what connects the two. -/
theorem equiv_denote_refine_full (t : Term) (p : Pred)
    (hq : ∀ v, (denote t).T v ↔ p.eval v = true) :
    Codec.Equiv (denote (.refine t p)) (denote t) := equiv_restrict_full _ _ hq

/-- §6: `μ(w(c)) = μ(c)` for the three codec wrappers. The two field wrappers are
    `optional_μ` and `optional_μ`, which are already stated over a denotation. -/
theorem denote_held_μ (t P : Term) (f g : Value → Value) :
    (denote (.held t P f g)).μ = (denote t).μ := rfl

theorem denote_refine_μ (t : Term) (p : Pred) :
    (denote (.refine t p)).μ = (denote t).μ := rfl

end Terms

end Calculus
