import Calculus.Discharge

/-!
# The n-ary literal is a union of singletons — what that union concludes

`(literal)` is one constructor carrying one value, `literal (k : GroundKind) (v : k.Carrier)`, and
a set of alternatives is a `Term.union` of singletons. **This file is what that union concludes**,
so the n-ary rule the specification writes is derived rather than assumed:

* `typed_literalsS` / `typed_literalsN` derive exactly what the old ~~Typed.literalS~~ and
  ~~Typed.literalN~~ concluded, from `Typed.literal` at a singleton and `Typed.union`. Same held
  set, same member.
* `dincomp_map_literal_str` / `_num` discharge §5's **(D)** from the alternatives being distinct.
* `uAtCan_map_literal_str` / `_num` discharge (U) **on both sides**, through
  `uniqueAdmission_of_sharedBase`.

The (U) one is worth stating plainly. Read from the *pair*, two numeric options are refinements
of one `numberCodec` at disjoint predicates, which is all `uniqueAdmission_of_sharedBase`
needs.
`uAtCan_of_literalN_disjoint` already made that argument for a union of n-ary numeric literals
and never used the n-ary constructor to make it — only the shared base — so it holds for
singletons too. The read-side row agrees, asking the codec rather than answering
`⊤`; the correction is recorded below and it does not change a line of this file's proofs,
which never appealed to the table.

**Why the statements take a bare `List` and not a `Finset`.** `Term.union` takes a `List Term`,
and bridging from a `NEFinset` is `Finset.toList`, which is `Multiset.toList`, which is
`Quotient.out` — `Classical.choice`. The first draft of this file was stated over `NEFinset` and
`#assert_axioms_all` rejected five theorems for exactly that. Stated over `(l : List α)` with
`l.Nodup` and `l ≠ []`, as it is here, it is choice-free, and those two premises are precisely the
gates the `℘⁺fin` repair had deleted. `Term` cannot have `DecidableEq` either (`Term.custom`
carries functions on `Value`), so `union` could not take a `NEFinset Term` and close the gap that
way.

**That obstruction is why the literal held a set for as long as it did, and it is why the set
could go.** The bridge is needed only to prove an n-ary *constructor* equal to the union. With one
value there is no `Finset` of alternatives anywhere, so nothing reaches `Finset.toList` and the
route is free.
-/
namespace Calculus

/-! ## The judgement

Stated over a bare `List`, by recursion on it, rather than over a `Finset` of alternatives: the
literal carries one value and the union carries a list, so there is no set to walk and nothing to
bridge. The two held sets below are `HLit` at one value and so are `rfl`, where a set of
alternatives needed a lemma to collapse the existential. -/

/-- Every option of a string literal set is derivable, at `S`. No premise: ~~LiteralD~~, the
    gate this used to carry beside the rule, was `true` at every base but `number`. -/
theorem typedListμ_map_literal_str : ∀ (l : List String),
    TypedListμ (l.map fun s => .literal .string s)
      (l.map fun s => fun v => v = Value.str s)
      (l.map fun _ => some Member.S)
  | [] => .nil
  | s :: rest => by
      refine .cons ?_ (typedListμ_map_literal_str rest)
      show Typed (Term.literal .string s) (fun v => v = Value.str s) (some .S)
      exact Typed.literal .string s

/-- …and of a numeric one, at `N`, with no premise: the list is a `List WFDouble`, so each
    element carries its own gate. -/
theorem typedListμ_map_literal_num : ∀ (l : List WFDouble),
    TypedListμ (l.map fun d => .literal .number d)
      (l.map fun d => fun v => v = Value.num d.1)
      (l.map fun _ => some Member.N)
  | [] => .nil
  | d :: rest => by
      refine .cons ?_ (typedListμ_map_literal_num rest)
      show Typed (Term.literal .number d) (fun v => v = Value.num d.1) (some .N)
      exact Typed.literal .number d

/-! ## The member, the held set, and (D) -/

/-- A union of options that all store the same member stores it. -/
theorem unanimous_map_const {α : Type} {m : Option Member} : ∀ (l : List α), l ≠ [] →
    unanimous (l.map fun _ => m) = m
  | [], h => absurd rfl h
  | _ :: rest, _ => by simp [unanimous]

/-- `⋃` of the singletons **is** `(literal-S)`'s held set. -/
theorem hunion_map_literal_str (l : List String) :
    HUnion (l.map fun s => fun v => v = Value.str s)
      = fun v => ∃ s, s ∈ l ∧ v = .str s := by
  funext v
  simp only [HUnion, List.mem_map, eq_iff_iff]
  constructor
  · rintro ⟨T, ⟨s, hs, rfl⟩, hv⟩; exact ⟨s, hs, hv⟩
  · rintro ⟨s, hs, rfl⟩; exact ⟨_, ⟨s, hs, rfl⟩, rfl⟩

/-- …and at the numeric base. -/
theorem hunion_map_literal_num (l : List WFDouble) :
    HUnion (l.map fun d => fun v => v = Value.num d.1)
      = fun v => ∃ d, d ∈ l ∧ v = .num d.1 := by
  funext v
  simp only [HUnion, List.mem_map, eq_iff_iff]
  constructor
  · rintro ⟨T, ⟨d, hd, rfl⟩, hv⟩; exact ⟨d, hd, hv⟩
  · rintro ⟨d, hd, rfl⟩; exact ⟨_, ⟨d, hd, rfl⟩, rfl⟩

/-- §5's **(D)** on a string literal set's options, from the alternatives being distinct —
    which is `NEFinset`'s, not a premise. Incomparability is the *easy* direction here: two
    distinct singletons contain each other in neither order. -/
theorem dincomp_map_literal_str {l : List String} (hnd : l.Nodup) :
    DIncomp (l.map fun s => fun v => v = Value.str s) := by
  rw [DIncomp, List.pairwise_map]
  refine hnd.imp ?_
  intro a b hab
  refine Or.inl ⟨fun h => hab ?_, fun h => hab ?_⟩
  · have h' : Value.str a = Value.str b := h (.str a) rfl
    simpa using h'
  · have h' : Value.str b = Value.str a := h (.str b) rfl
    exact (by simpa using h' : b = a).symm

/-- …and the same at the numeric base. -/
theorem dincomp_map_literal_num {l : List WFDouble} (hnd : l.Nodup) :
    DIncomp (l.map fun d => fun v => v = Value.num d.1) := by
  rw [DIncomp, List.pairwise_map]
  refine hnd.imp ?_
  intro a b hab
  refine Or.inl ⟨fun h => hab ?_, fun h => hab ?_⟩
  · have h' : Value.num a.1 = Value.num b.1 := h (.num a.1) rfl
    exact Subtype.ext (by simpa using h')
  · have h' : Value.num b.1 = Value.num a.1 := h (.num b.1) rfl
    exact (Subtype.ext (by simpa using h') : b = a).symm

/-! ## (U) at the numeric base

**`AdmA` does not need to *name* the attributes that read into `ℓ`, only to decide one.** The
tempting inference is that it does: the stored text goes through `Double.ofDec`, and no
syntactic set of attributes names the numerals reading into a given value. That is a fact about
*values*. `ofDec` is a **function** — a stored numeral reads to at most one double, and one
double cannot inhabit two disjoint sets — so the answer is unique without being nameable, and
the row obtains it by calling the codec.

So `AdmALit`'s `.number` row is `((literalCodec .number ls).p ·).isSome`, which separates two
disjoint numeric literals term by term.

The pair reading is not superseded and is the one used below: `uniqueAdmission_of_sharedBase`
settles an `n`-ary family on both sides in one step where the table settles a pair at a time.
Each option is `numberCodec.restrict` at a predicate, the predicates are disjoint, and that is
the hypothesis — which needs only the shared base, never the n-ary constructor, so it holds
here with `ℓ` as `Finset` data. -/

/-- (U) on both sides for a string literal set's options. -/
theorem uAtCan_map_literal_str {l : List String} (hnd : l.Nodup) :
    UAtCan (l.map fun s => .literal .string s) := by
  show UniqueAdmission (semsOf _)
  have hs : semsOf (l.map fun s => .literal .string s)
      = (l.map fun s => literalCodec .string s).map OptionSem.byAttempt := by
    simp [semsOf, List.map_map, specOf, optionSemOf, denote]
  rw [hs]
  refine uniqueAdmission_of_sharedBase (base := baseCodec .string)
    (qs := l.map fun s => inL .string s)
    (lawful_baseCodec .string).core ?_ ?_
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun s _ =>
      ⟨literalCodec_e_restrict .string s, literalCodec_p_restrict .string s⟩
  · rw [List.pairwise_map]
    refine hnd.imp ?_
    intro a b hab v hv
    cases v <;> simp_all [inL]

/-- …and at the numeric base, by the same shared-base route: `n`-ary and both sides in one
    step, which is what this route buys over a pairwise separation read off the table. -/
theorem uAtCan_map_literal_num {l : List WFDouble} (hnd : l.Nodup) :
    UAtCan (l.map fun d => .literal .number d) := by
  show UniqueAdmission (semsOf _)
  have hs : semsOf (l.map fun d => .literal .number d)
      = (l.map fun d => literalCodec .number d).map OptionSem.byAttempt := by
    simp [semsOf, List.map_map, specOf, optionSemOf, denote]
  rw [hs]
  refine uniqueAdmission_of_sharedBase (base := baseCodec .number)
    (qs := l.map fun d => inL .number d)
    (lawful_baseCodec .number).core ?_ ?_
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun d _ =>
      ⟨literalCodec_e_restrict .number d, literalCodec_p_restrict .number d⟩
  · rw [List.pairwise_map]
    refine hnd.imp ?_
    intro a b hab v hv
    cases v
    case num d =>
      -- the gate is `inL`'s now, on both the hypothesis and the goal
      cases hw : Numeral.WF d.toDec with
      | false => simp [inL, hw] at hv
      | true =>
        simp only [inL, hw, dite_true, decide_eq_true_eq] at hv
        simp only [inL, hw, dite_true, decide_eq_false_iff_not, hv]
        exact hab
    all_goals simp_all [inL]

/-! ## The two rules, derived — over a `List`, and that is the finding

The specification writes `(literal-S)`'s payload as a set; `Term.union`'s is a `List Term`. Going
from one to the other is `Finset.toList`, which is `Multiset.toList`, which is `Quotient.out` —
and every theorem stated through it picks up `Classical.choice`. The axiom scan says so: the first
draft of this file stated the two rules over `NEFinset` and five theorems came back unsanctioned.

So they are stated over a list with the two premises spelled out, which is choice-free and is the
honest shape of the claim. `hnd` and `hne` are what the set was carrying, and writing them out is
what lets the term language carry no set at all. -/

/-- **`(literal-S)` is derivable.** Every part of ~~Typed.literalS~~'s conclusion — the held set and
    the member — comes from `Typed.literal` and `Typed.union`, with no premise ~~literalS~~ does not
    already have: `hnd` and `hne` are what `NEFinset` was carrying. -/
theorem typed_literalsS {l : List String} (hnd : l.Nodup) (hne : l ≠ []) :
    Typed (.union (l.map fun s => .literal .string s))
      (fun v => ∃ s, s ∈ l ∧ v = .str s) (some .S) := by
  have h := Typed.union (typedListμ_map_literal_str l) (dincomp_map_literal_str hnd)
  rw [hunion_map_literal_str, unanimous_map_const _ hne] at h
  exact h

/-- **`(literal-N)` is derivable**, and §3's `ℓ ⊆ D` is the list's element type. -/
theorem typed_literalsN {l : List WFDouble} (hnd : l.Nodup) (hne : l ≠ []) :
    Typed (.union (l.map fun d => .literal .number d))
      (fun v => ∃ d, d ∈ l ∧ v = .num d.1) (some .N) := by
  have h := Typed.union (typedListμ_map_literal_num l) (dincomp_map_literal_num hnd)
  rw [hunion_map_literal_num, unanimous_map_const _ hne] at h
  exact h

/-! ## The other route not taken: `literal` as a refinement

`refine(base, · ∈ ℓ)` is the second derivation of `literal`, and until now it cost precision:
`admA (.refine t q)` dropped `q`, so the refinement form was **blind on the read side** where
the read-side literal row was not. That was the argument against a literal API in which every primitive codec
accepts its own alternatives — `string('A')`, `number(1)`, `decimal('1')` — since the natural
encoding of that API is a refinement.

The argument is gone with the row. `AdmA` at a `refine` decodes with the base and applies `q`,
and `literalCodec k ls` **is** `(baseCodec k).restrict (inL k ls)`, so the two terms denote the
same read and the two rows now compute the same answer, at every base including `number`.

On the write side the refinement is not merely equal but **strictly sharper at `number`**:
`adm (.literal k ls)` is `inL k ls` alone, which over-approximates there (`dom(e)` is `inL`
*and* `WF d.toDec` — the fourth row `b52910d` left standing), while the refinement conjoins the
base's own `inD`. -/

/-- The term denoting a ground base, as an index. `baseCodec`'s counterpart one level up. -/
def groundTerm : GroundKind → Term
  | .string => .string
  | .number => .number
  | .decimal => .decimal
  | .boolean => .boolean
  | .binary => .binary
  | .null => .null

theorem denote_groundTerm (k : GroundKind) : denote (groundTerm k) = baseCodec k := by
  cases k <;> rfl

/-- **`refine(base k, ∈ ℓ)` reads exactly the base restricted to `ℓ`**, up to the held set a
    literal carries — which `restrict` cannot know and `T` is not consulted by either row.

    Stated over the refinement's own `Finset`, because that is what `Pred.members` carries. A
    literal is the one-alternative case of the same restriction: `literalCodec k x` is
    `(baseCodec k).restrict (inL k x)` by definition, and `inLs` at a singleton is `inL`. -/
theorem denote_refine_ground_p (k : GroundKind) (ls : NEFinset k.Carrier) (a : Attr) :
    (denote (.refine (groundTerm k) (.members k ls))).p a
      = ((baseCodec k).restrict (inLs k ls)).p a := by
  cases k <;> rfl





end Calculus
