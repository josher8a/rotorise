import Calculus.Dynamo.Witness.Discharge

variable {α : Calculus.Table}

/-!
# The n-ary literal is a union of singletons — what that union concludes

`(literal)` is one constructor carrying one value, `literal (k : GroundKind) (v : k.Carrier)`, and
a set of alternatives is a `Term.union` of singletons. **This file is what that union concludes**,
so the n-ary rule the specification writes is derived rather than assumed:

* `typed_literalsS` / `typed_literalsN` derive exactly what the old ~~Typed.literalS~~ and
  ~~Typed.literalN~~ concluded, from `Typed.literal` at a singleton and `Typed.union`. Same held
  set, same member.

**Why the statements take a bare `List` and not a `Finset`.** `Term.union` takes a `List Term`,
and bridging from a `NEFinset` is `Finset.toList`, which is `Multiset.toList`, which is
`Quotient.out` — `Classical.choice`. The first draft of this file was stated over `NEFinset` and
`#assert_axioms_all` rejected five theorems for exactly that. Stated over `(l : List α)` with
`l.Nodup` and `l ≠ []`, as it is here, it is choice-free, and those two premises are precisely the
gates the `℘⁺fin` repair had deleted. `Term` cannot have `DecidableEq` either (`Term.held`
carries two functions on `Value`, and `Pred.closure` carries one), so `union` could not take a
`NEFinset Term` and close the gap that way.

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
    TypedListμ α (l.map fun s => .literal .string s)
      (l.map fun s => fun v => v = Value.str s)
      (l.map fun _ => some Member.S)
  | [] => .nil
  | s :: rest => by
      refine .cons ?_ (typedListμ_map_literal_str rest)
      show Typed α (Term.literal .string s) (fun v => v = Value.str s) (some .S)
      exact Typed.literal .string s

/-- …and of a numeric one, at `N`, with no premise: the list is a `List WFNumeral`, so each
    element carries its own gate. -/
theorem typedListμ_map_literal_num : ∀ (l : List WFNumeral),
    TypedListμ α (l.map fun d => .literal .number d)
      (l.map fun d => fun v => v = Value.num d)
      (l.map fun _ => some Member.N)
  | [] => .nil
  | d :: rest => by
      refine .cons ?_ (typedListμ_map_literal_num rest)
      show Typed α (Term.literal .number d) (fun v => v = Value.num d) (some .N)
      exact Typed.literal .number d

/-! ## The member and the held set -/

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
theorem hunion_map_literal_num (l : List WFNumeral) :
    HUnion (l.map fun d => fun v => v = Value.num d)
      = fun v => ∃ d, d ∈ l ∧ v = .num d := by
  funext v
  simp only [HUnion, List.mem_map, eq_iff_iff]
  constructor
  · rintro ⟨T, ⟨d, hd, rfl⟩, hv⟩; exact ⟨d, hd, hv⟩
  · rintro ⟨d, hd, rfl⟩; exact ⟨_, ⟨d, hd, rfl⟩, rfl⟩

/-! ## The two rules, derived — over a `List`, and that is the finding

The specification writes `(literal-S)`'s payload as a set; `Term.union`'s is a `List Term`. Going
from one to the other is `Finset.toList`, which is `Multiset.toList`, which is `Quotient.out` —
and every theorem stated through it picks up `Classical.choice`. The axiom scan says so: the first
draft of this file stated the two rules over `NEFinset` and five theorems came back unsanctioned.

So they are stated over a list with the premise spelled out, which is choice-free and is the
honest shape of the claim. `hne` is what the set was carrying for the member, and writing it out
is what lets the term language carry no set at all. -/

/-- **`(literal-S)` is derivable.** Every part of ~~Typed.literalS~~'s conclusion — the held set and
    the member — comes from `Typed.literal` and `Typed.union`, with no premise ~~literalS~~ does not
    already have: `hne` is what `NEFinset` was carrying for the member. -/
theorem typed_literalsS {l : List String} (hne : l ≠ []) :
    Typed α (.union (l.map fun s => .literal .string s))
      (fun v => ∃ s, s ∈ l ∧ v = .str s) (some .S) := by
  have h := Typed.union (α := α) (typedListμ_map_literal_str l)
  rw [hunion_map_literal_str, unanimous_map_const _ hne] at h
  exact h

/-- **`(literal-N)` is derivable**, and §3's `ℓ ⊆ D` is the list's element type. -/
theorem typed_literalsN {l : List WFNumeral} (hne : l ≠ []) :
    Typed α (.union (l.map fun d => .literal .number d))
      (fun v => ∃ d, d ∈ l ∧ v = .num d) (some .N) := by
  have h := Typed.union (α := α) (typedListμ_map_literal_num l)
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

/-- **`refine(base k, ∈ ℓ)` reads exactly the base restricted to `ℓ`**, up to the held set a
    literal carries — which `restrict` cannot know and `T` is not consulted by either row.

    Stated over the refinement's own `Finset`, because that is what `Pred.members` carries. A
    literal is the one-alternative case of the same restriction: `literalCodec k x` is
    `(baseCodec k).restrict (inL k x)` by definition, and `inLs` at a singleton is `inL`. -/
theorem denote_refine_ground_p (k : GroundKind) (ls : NEFinset k.Carrier) (a : Attr) :
    (denote α (.refine (.base k) (.members k ls))).p a
      = ((baseCodec k).restrict (inLs k ls)).p a := by
  cases k <;> rfl





end Calculus
