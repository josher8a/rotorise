import Calculus.Dynamo.Analysis.ExactA

variable {α : Calculus.Table}

/-!
# Orthogonality: separation

`Obligations (.union opts)` carries pairwise compatibility. Two separated options are compatible
(`pairwiseCompat_of_separated`). The decidable certificate is `certPair` (`Meet.lean`): two
options are orthogonal when the domains and the ranges of the two terms meet at the bottom. The
meet refuses a closure beside a partner that its inner term does not meet at the bottom.

This module holds `Separates` and the two theorems that the discharger reads from it.

## Sound, never complete, and why there is no `unknown`

Semantic orthogonality is undecidable in this language — `refine t q` carries an arbitrary
`Value → Bool` and `held t P f g` an arbitrary pair of maps. So the certificate answers a
*narrower* question, and the answer `false` means "no certificate", never "not orthogonal".
An opaque subterm admits every input, so a pair with an opaque option and a nonempty partner is
not separated.

## Both halves of the pair

`Separates` takes **two** families, one over `Value` and one over `Attr`, and asks each to be
pairwise disjoint. A pair can be separated on one side and not on the other, and then it is not
separated. `held` is the witness: it writes what its caller-side term admits, and it reads what
its stored-side term reads. So `union(held(string, number, f, g), string)`, the decimal adapter
against a string, separates on the write side and meets on the read side.
-/

namespace Calculus

/-! ## Separation

Two options are separated when no input is admitted by both. -/

variable (α) in
/-- **What the discharger consumes.** Both families disjoint, as a `Prop`, of which the
    certificate is the decidable part. A new certificate is a new theorem producing `Separates`,
    not a new case in `pairwiseCompat_of_separated`. -/
def Separates (x y : Term) : Prop :=
  (∀ v, Adm α x v = true → ¬ Adm α y v = true) ∧ (∀ a, AdmA α x a = true → ¬ AdmA α y a = true)

variable (α) in
/-- **The whole premise the discharger takes**, as one name: every pair of options separated.

    `Separates` is the rule for a pair and this is the rule for a list, so the certificate
    produces the first and a caller supplies the second.

    **It names the guarantee where the guarantee already lives, and moves nothing.** `Typed.union`
    cannot take it: `Separates` is stated on `Adm`, in `ExactV.lean`, and
    the import chain is `Typing` then `Soundness` then `ExactV` then `ExactA` then this
    file. A premise here is four modules above the judgement it would constrain. So an undischarged
    union stays *underivable* through `Obligations`, which is where it was, rather than becoming
    unrepresentable.

    **And unrepresentable is not available anyway.** A `Term.union` carrying its own witness needs
    either an inductive indexed by the option list it constrains, which is induction-induction, or
    a field whose type is computed from the term, which is induction-recursion. Lean 4 rejects both:
    the first as `unknown identifier` on the type being defined, the second as `invalid mutual
    block: either all elements of the block must be inductive/structure declarations, or they must
    all be definitions`. The one shape that works is a pre-term with a well-formedness subtype, and
    that re-founds the term language. -/
def Separated (opts : List Term) : Prop := List.Pairwise (Separates α) opts

/-- **Pairwise separation bounds the admitters at one.** Separation says no two options admit
    one input. -/
theorem admitsAtMostOne_of_separated {opts : List Term} (h : Separated α opts) :
    AdmitsAtMostOne (denoteList α opts) := by
  constructor
  · intro v
    rw [filter_AdmList (fun t _ => Adm_exact t) v, List.length_map]
    refine length_le_one_of_pairwise_false (List.Pairwise.imp_of_mem ?_
      (List.Pairwise.filter _ (h.imp fun hs => hs.1 v)))
    intro x y hx hy hxy
    have hax : Adm α x v = true := (List.mem_filter.mp hx).2
    have hay : Adm α y v = true := (List.mem_filter.mp hy).2
    exact hxy hax hay
  · intro a
    rw [filter_AdmAList (fun t _ => AdmA_exact t) a, List.length_map]
    refine length_le_one_of_pairwise_false (List.Pairwise.imp_of_mem ?_
      (List.Pairwise.filter _ (h.imp fun hs => hs.2 a)))
    intro x y hx hy hxy
    have hax : AdmA α x a = true := (List.mem_filter.mp hx).2
    have hay : AdmA α y a = true := (List.mem_filter.mp hy).2
    exact hxy hax hay

/-- Two members that both meet `P`, in a list where no related pair both meets `P`, are one. -/
theorem eq_of_pairwise_excl {α : Type} {P : α → Prop} {R : α → α → Prop}
    (hR : ∀ x y, R x y → P x → P y → False) :
    ∀ {l : List α}, l.Pairwise R → ∀ x ∈ l, ∀ y ∈ l, P x → P y → x = y
  | [], _, _, hx, _, _, _, _ => nomatch hx
  | h :: tl, hp, x, hx, y, hy, px, py => by
    have hp' := List.pairwise_cons.mp hp
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · rfl
    · exact (hR _ _ (hp'.1 y hy') px py).elim
    · exact (hR _ _ (hp'.1 x hx') py px).elim
    · exact eq_of_pairwise_excl hR hp'.2 x hx' y hy' px py

/-- **Pairwise separation gives the union's obligation.** No input reaches two separated
    options, so an option never acts where another reads. -/
theorem pairwiseCompat_of_separated {opts : List Term}
    (hlaw : ∀ t ∈ opts, Lawful (denote α t)) (h : Separated α opts) : PairwiseCompat α opts := by
  intro s hs t ht a v hp hact
  have hsA : AdmA α s a = true := (AdmA_exact (α := α) s a).mpr (by rw [hp]; rfl)
  have hsV : Adm α s v = true := (Adm_exact (α := α) s v).mpr ((hlaw s hs).defined hp)
  have hst : t = s := by
    rcases hact with hq | he
    · have htA : AdmA α t a = true := (AdmA_exact (α := α) t a).mpr hq
      exact eq_of_pairwise_excl (P := fun u => AdmA α u a = true)
        (fun x y hxy px py => hxy.2 a px py) h t ht s hs htA hsA
    · have htV : Adm α t v = true := (Adm_exact (α := α) t v).mpr he
      exact eq_of_pairwise_excl (P := fun u => Adm α u v = true)
        (fun x y hxy px py => hxy.1 v px py) h t ht s hs htV hsV
  subst hst; exact hp

/-- Each codec is compatible with itself. -/
theorem compat_self (c : Codec) : Compat c c := fun _ _ hp _ => hp

/-- **An empty option is compatible with every option**: `never` reads nothing and writes
    nothing, so neither side of `Compat` has a case. -/
theorem compat_never_left (c : Codec) : Compat (denote α .never) c := fun _ _ hp _ => nomatch hp

/-- …and on the other side. -/
theorem compat_never_right (c : Codec) : Compat c (denote α .never) := fun _ _ _ hact => by
  rcases hact with h | h <;> exact nomatch h

/-- **A union with an empty option meets its obligation**, whatever the other option is. -/
theorem pairwiseCompat_never_right (x : Term) : PairwiseCompat α [x, .never] := by
  intro s hs t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs ht
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
    first | exact compat_self _ | exact compat_never_left _ | exact compat_never_right _

/-- …and with the empty option first. -/
theorem pairwiseCompat_never_left (x : Term) : PairwiseCompat α [.never, x] := by
  intro s hs t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs ht
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
    first | exact compat_self _ | exact compat_never_left _ | exact compat_never_right _

end Calculus
