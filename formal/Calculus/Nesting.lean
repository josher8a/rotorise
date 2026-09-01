import Calculus.Soundness

/-!
# §1's nesting bound, and the claim the calculus cannot make

`Domain.lean` states the bound: `Attr.Storable a` is `Attr.nesting a ≤ 32`, counting `L` and
`M` and nothing else. This file says what the calculus does and does not guarantee about it,
and the answer is worth stating precisely because **it is the one place `𝔸` is larger in the
model than in the store**.

Everywhere else §1 is exact, and (W) plus `Carrier` give `ran(e) ⊆ 𝔸` outright. Here they do
not: `Attr.l` and `Attr.m` nest without limit by construction, so a derivable term can write
an attribute the store refuses. That is not a defect the model *has* — it is a defect the
model must be able to **state**, because a target certified against a spec that cannot say
this would be certified against a claim weaker than the one its users read.

Three things are proved:

* **the ground fragment is safe** — every ground term writes nesting `0`, so the bound is
  never a question for the terms that do not nest;
* **the containers are exact** — `array` adds exactly one level, which is what makes the
  bound compositional rather than a global search;
* **and the calculus admits a term that breaks it** (`not_storable_of_typed`) — a *derivable*
  term, a value on its held set, and an encoding outside `Storable`. So `ran(e) ⊆ 𝔸` holds
  against the model's `𝔸` and fails against the store's, and there is a witness rather than a
  remark.

The third is why `src/` gates on depth at `opaque` and `native` (§12.6 of `codec-audit.md`)
and why a recursive typed codec is a live gap (item 19). It is also why the honest repair is
*not* a carrier refinement: the witness is well-typed, so no premise of the typing rules is
being violated — the rules simply do not mention depth.
-/

namespace Calculus

/-! ## The ground fragment writes flat -/

/-- Every ground codec writes a scalar or a wire set, and neither is a document type. -/
theorem nesting_zero_of_ground (k : GroundKind) (v : Value) (a : Attr)
    (h : (baseCodec k).e v = some a) : Attr.nesting a = 0 := by
  -- every branch writes a *named* constructor, so the work is substituting the equation the
  -- codec's `e` leaves behind and reading `nesting` off it
  cases k <;> cases v <;>
    simp_all [baseCodec, stringCodec, numberCodec, decimalCodec, booleanCodec, binaryCodec,
              nullCodec] <;>
    first
      | rfl
      | (subst_vars; rfl)
      | (obtain ⟨-, rfl⟩ := h; rfl)

/-! ## The containers add exactly one

Compositional in both directions, which is what a bound has to be if it is to be checked
anywhere but at the top: `array` adds one level and nothing else, so a nesting budget divides
down a term rather than being recomputed at every node. -/

/-- A written list nests one deeper than its deepest element. -/
theorem nesting_l (as : List Attr) :
    Attr.nesting (.l as) = Attr.nestingL as + 1 := rfl

/-- And an element never nests deeper than the list holding it. -/
theorem nestingL_of_mem {as : List Attr} {a : Attr} (h : a ∈ as) :
    Attr.nesting a ≤ Attr.nestingL as := by
  induction as with
  | nil => exact absurd h (by simp)
  | cons b bs ih =>
    rcases List.mem_cons.mp h with rfl | h'
    · exact Nat.le_max_left _ _
    · exact le_trans (ih h') (Nat.le_max_right _ _)

/-! ## The witness: a derivable term outside the store's `𝔸`

Stated over a family rather than a literal 33-deep term, so the proof is an induction and not
thirty-three unfoldings — and so the bound can move without the witness being rewritten. -/

/-- `n` nested `array`s over `string`. -/
def deepT : Nat → Term
  | 0 => .string
  | n + 1 => .array (deepT n)

/-- A value on its held set: `n` nested one-element arrays over a string. -/
def deepV : Nat → Value
  | 0 => .str ""
  | n + 1 => .arr [deepV n]

/-- What the pair writes: `n` nested `L`s over an `S`. -/
def deepA : Nat → Attr
  | 0 => .s ""
  | n + 1 => .l [deepA n]

/-- The nesting is the index, on the nose — `S` is not a document type and each `L` is one. -/
theorem nesting_deepA : ∀ n, Attr.nesting (deepA n) = n
  | 0 => rfl
  | n + 1 => by
    show Attr.nestingL [deepA n] + 1 = n + 1
    show max (Attr.nesting (deepA n)) 0 + 1 = n + 1
    rw [nesting_deepA n]; simp

/-- Every one of them is derivable. -/
theorem typed_deepT : ∀ n, ∃ T μ, Typed (deepT n) T μ
  | 0 => ⟨_, _, Typed.string⟩
  | n + 1 => by
    obtain ⟨T, μ, h⟩ := typed_deepT n
    exact ⟨_, _, Typed.array h⟩

/-- And every one of them writes what the index says. -/
theorem deepT_e : ∀ n, (denote (deepT n)).e (deepV n) = some (deepA n)
  | 0 => rfl
  | n + 1 => by
    show (arrayCodec (denote (deepT n))).e (.arr [deepV n]) = some (.l [deepA n])
    simp only [arrayCodec, traverse, deepT_e n]
    rfl

/-- **The claim the calculus cannot make.** A derivable term, a value it writes, and an
    attribute the store refuses — so `ran(e) ⊆ 𝔸` is exact against the model's `𝔸` and false
    against DynamoDB's.

    The term is `array^33(string)`, which carries no premise about depth because §3 states
    none. That is the finding: the bound is not a side condition anyone forgot to discharge,
    it is absent from the rules, and no derivation can be blamed. -/
theorem not_storable_of_typed :
    ∃ (t : Term) (T : Held) (μ : Option Member) (v : Value) (a : Attr),
      Typed t T μ ∧ (denote t).e v = some a ∧ ¬ Attr.Storable a := by
  obtain ⟨T, μ, hty⟩ := typed_deepT (maxNesting + 1)
  refine ⟨_, T, μ, deepV (maxNesting + 1), deepA (maxNesting + 1), hty,
    deepT_e (maxNesting + 1), ?_⟩
  show ¬ Attr.nesting (deepA (maxNesting + 1)) ≤ maxNesting
  rw [nesting_deepA]
  omega

/-- The boundary, both sides, so a change to `maxNesting` moves one number and not a proof. -/
theorem storable_deepA_maxNesting : Attr.Storable (deepA maxNesting) := by
  show Attr.nesting (deepA maxNesting) ≤ maxNesting
  rw [nesting_deepA]

end Calculus
