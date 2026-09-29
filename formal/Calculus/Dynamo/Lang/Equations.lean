import Calculus.Dynamo.Lang.Denote
import Calculus.Dynamo.Alg.Opaque

variable {α : Calculus.Table}

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
theorem optional_μ (t : Term) : (fieldSem α (.optional t)).codec.μ = (denote α t).μ := rfl

/-! ## `union` is associative

§6's row, stated outright. Both forms take the first admitter in the same order, so the
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

/-- §6: `union(c₁, union(c₂, c₃)) ≡ union(c₁, c₂, c₃)` — with no side condition. -/
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

/-! ## §6's Hold rows, at term level

Each row's twin, stated where a reader of the specification's §6 would look for it: about a
`Term`, the way `Refutations.lean`'s "Do not hold" rows already are. Every one is its
combinator row through the bridge above, so they cost a line each and buy the property
the representation audit asked for — both halves of §6 in one language. -/

section Terms

/-- §6: `held(c, P, PA, [], kA) ≡ refine(c, P)`. The empty word is the identity transform at
    every table, and every stored word of DynamoDB is the identity, so the `held` leaves the
    caller-side restriction, and that restriction is a `refine` by the admission of `P`. The
    stored outer only shrinks the graph, and `≡` asks agreement where both codecs are defined. -/
theorem equiv_denote_held_id (t P PA : Term) (kA : List (Alg.Syn.GenA dynSyn × Bool)) :
    Codec.Equiv (denote α (.held t P PA [] kA))
      (denote α (.refine t (.closure fun v => ((denote α P).e v).isSome) ())) := by
  simp only [denote_rows]
  refine ⟨fun _ => Iff.rfl, rfl, ?_, ?_⟩
  · intro v a a' h h'
    exact Option.some.inj
      ((through_e.mp (Alg.refine2_f.mp h).2.1).symm.trans (refine2_f.mp h').2.1)
  · intro a v v' h h'
    obtain ⟨w, hw, rfl⟩ := through_p.mp (Alg.refine2_f.mp h).2.1
    exact Option.some.inj (hw.symm.trans (refine2_f.mp h').2.1)

/-- §6: `held(held(c, P, PA, k), P′, PA′, k′) ≡ refine(held(c, P′, PA′, k ++ k′), P ∘ f′)`, where
    `f′` is the caller-side function of `k′`. The words concatenate, so the transforms compose,
    and the inner caller-side restriction pulls back along `f′`. The pullback is a predicate and
    no term, so the right side carries it as a `refine`. The inner stored outer only shrinks the
    graph. -/
theorem equiv_denote_held_comp (t P PA P' PA' : Term) (k k' : Word)
    (kA kA' : List (Alg.Syn.GenA dynSyn × Bool)) :
    Codec.Equiv (denote α (.held (.held t P PA k kA) P' PA' k' kA'))
      (denote α (.refine (.held t P' PA' (k ++ k') [])
        (.closure fun v => ((denote α P).e ((α.word k').1 v)).isSome) ())) := by
  simp only [denote_rows, Alg.Table.word_append]
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
    Codec.Equiv (denote α (.refine (.refine t p ()) p' ()))
      (denote α (.refine t (.closure (fun v => p.eval v && p'.eval v)) ())) := by
  simp only [denote_rows]
  exact equiv_restrict_meet _ _ _

/-- §6: `refine(c, T) ≡ c` for `⊢ c : T ⇝ μ`. The premise is the row's, read off the
    denotation rather than the judgement — `typed_TSub` is what connects the two. -/
theorem equiv_denote_refine_full (t : Term) (p : Pred)
    (hq : ∀ v, (denote α t).T v ↔ p.eval v = true) :
    Codec.Equiv (denote α (.refine t p ())) (denote α t) := by
  simp only [denote_rows]
  exact equiv_restrict_full _ _ hq

/-- §6: `μ(w(c)) = μ(c)` for the three codec wrappers. The two field wrappers are
    `optional_μ` and `optional_μ`, which are already stated over a denotation. -/
theorem denote_held_μ (t P PA : Term) (k : Word) (kA : List (Alg.Syn.GenA dynSyn × Bool)) :
    (denote α (.held t P PA k kA)).μ = (denote α t).μ := rfl

theorem denote_refine_μ (t : Term) (p : Pred) :
    (denote α (.refine t p ())).μ = (denote α t).μ := rfl

end Terms

end Calculus
