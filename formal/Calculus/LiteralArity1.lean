import Calculus.Discharge

/-!
# The n-ary literal is derivable from arity one

`(literal-S)` and `(literal-N)` are constructors of `Term`, and §3 has **one** `(literal)` rule.
This file asks whether the two n-ary constructors are *rules* at all, or whether they are the
union of arity-one literals wearing a rule's clothes — and the answer is the latter, on every
count the constructors are used for.

The three things a rule has to supply are the judgement, §5's **(D)**, and (U):

* `typed_literalsS` / `typed_literalsN` derive **exactly `Typed.literalS`/`Typed.literalN`'s
  conclusion** from `Typed.literal` and `Typed.union`. The held set is the same set, the member
  is the same member.
* `dincomp_literalsS` / `dincomp_literalsN` discharge (D) from the alternatives being distinct,
  which `NEFinset` already gives.
* `uAtCan_literalsS` / `uAtCan_literalsN` discharge (U) **on both sides**, through
  `uniqueAdmission_of_sharedBase`.

The last one is the one worth stating plainly, because the §5 table says the opposite. `admA`
sends a numeric literal to `⊤` — `admA_literalN_blind` — so read from the table, two numeric
options never separate on the read side and a union of them cannot resolve. Read from the *pair*,
they are refinements of one `numberCodec` at disjoint predicates, and that is all
`uniqueAdmission_of_sharedBase` needs. `uAtCan_of_literalN_disjoint` already made this argument
for a union of `literalN`s; the point here is that it never needed the n-ary constructor, only
the shared base — so it holds for a union of arity-*one* literals, where `ℓ` is `Finset` data
rather than a term's payload.

This does not delete anything by itself. It is the evidence that deleting the two constructors
loses no derivable judgement — the check that has to come before the 266-site edit, not after.
-/

namespace Calculus

/-! ## The judgement

Stated over a bare `List` and applied to `Finset.toList`, rather than by induction on
`ls.1.toList` — the list is not a variable there, so the motive does not generalise. The same
shape the object-field work settled on. -/

/-- Every option of a string literal set is derivable, at `S`. No premise: `literalD` is `true`
    at every base but `number`. -/
theorem typedListμ_map_literal_str : ∀ (l : List String),
    TypedListμ (l.map fun s => .literal (.str s))
      (l.map fun s => fun v => v = Value.str s)
      (l.map fun _ => some Member.S)
  | [] => .nil
  | s :: rest => .cons (Typed.literal (.str s) rfl) (typedListμ_map_literal_str rest)

/-- …and of a numeric one, at `N`, on `ℓ ⊆ D` — the premise `(literal-N)` carries as `hD`, here
    consumed one element at a time by the arity-one rule. It is not weakened and not absorbed:
    §2.2 of the audit is the reason that matters. -/
theorem typedListμ_map_literal_num : ∀ (l : List Double),
    (∀ d ∈ l, Numeral.WF d.toDec = true) →
    TypedListμ (l.map fun d => .literal (.num d))
      (l.map fun d => fun v => v = Value.num d)
      (l.map fun _ => some Member.N)
  | [], _ => .nil
  | d :: rest, h =>
      .cons (Typed.literal (.num d) (h d (List.mem_cons_self _ _)))
        (typedListμ_map_literal_num rest fun x hx => h x (List.mem_cons_of_mem _ hx))

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
theorem hunion_map_literal_num (l : List Double) :
    HUnion (l.map fun d => fun v => v = Value.num d)
      = fun v => ∃ d, d ∈ l ∧ v = .num d := by
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
  refine ⟨fun h => hab ?_, fun h => hab ?_⟩
  · have h' : Value.str a = Value.str b := h (.str a) rfl
    simpa using h'
  · have h' : Value.str b = Value.str a := h (.str b) rfl
    exact (by simpa using h' : b = a).symm

/-- …and the same at the numeric base. -/
theorem dincomp_map_literal_num {l : List Double} (hnd : l.Nodup) :
    DIncomp (l.map fun d => fun v => v = Value.num d) := by
  rw [DIncomp, List.pairwise_map]
  refine hnd.imp ?_
  intro a b hab
  refine ⟨fun h => hab ?_, fun h => hab ?_⟩
  · have h' : Value.num a = Value.num b := h (.num a) rfl
    simpa using h'
  · have h' : Value.num b = Value.num a := h (.num b) rfl
    exact (by simpa using h' : b = a).symm

/-! ## (U), which the §5 table says is impossible at the numeric base

`admA_literalN_blind`: the read side of a numeric literal is `⊤`, because the stored text goes
through `Double.ofDec` and no syntactic set of attributes bounds one value. Two numeric options
therefore never separate *in the table*. They separate in the **pair**: each is
`numberCodec.restrict` at a predicate, the predicates are disjoint, and that is exactly
`uniqueAdmission_of_sharedBase`'s hypothesis. `uAtCan_of_literalN_disjoint` made this argument
for a union of `literalN`s — and never used the n-ary constructor for it, only the shared base,
which is why it holds here with `ℓ` as `Finset` data instead. -/

/-- (U) on both sides for a string literal set's options. -/
theorem uAtCan_map_literal_str (fuel : Nat) {l : List String} (hnd : l.Nodup) :
    UAtCan (fuel+1) (l.map fun s => .literal (.str s)) := by
  show UniqueAdmission (semsOf (fuel+1) _)
  have hs : semsOf (fuel+1) (l.map fun s => .literal (.str s))
      = (l.map fun s => literalCodec (.str s)).map OptionSem.byAttempt := by
    simp [semsOf, List.map_map, specOf, optionSemOf, denote]
  rw [hs]
  refine uniqueAdmission_of_sharedBase (base := stringCodec)
    (qs := l.map fun s => (fun w => match w with | .str s' => decide (s' = s) | _ => false))
    lawful_stringCodec.core ?_ ?_
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun s _ => ⟨rfl, rfl⟩
  · rw [List.pairwise_map]
    refine hnd.imp ?_
    intro a b hab v hv
    cases v with
    | str s =>
      simp only [decide_eq_true_eq] at hv
      subst hv
      simp only [decide_eq_false_iff_not]
      exact hab
    | _ => exact Bool.noConfusion hv

/-- …and at the numeric base, where the table cannot. -/
theorem uAtCan_map_literal_num (fuel : Nat) {l : List Double} (hnd : l.Nodup) :
    UAtCan (fuel+1) (l.map fun d => .literal (.num d)) := by
  show UniqueAdmission (semsOf (fuel+1) _)
  have hs : semsOf (fuel+1) (l.map fun d => .literal (.num d))
      = (l.map fun d => literalCodec (.num d)).map OptionSem.byAttempt := by
    simp [semsOf, List.map_map, specOf, optionSemOf, denote]
  rw [hs]
  refine uniqueAdmission_of_sharedBase (base := numberCodec)
    (qs := l.map fun d => (fun w => match w with | .num d' => decide (d' = d) | _ => false))
    lawful_numberCodec.core ?_ ?_
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun d _ => ⟨rfl, rfl⟩
  · rw [List.pairwise_map]
    refine hnd.imp ?_
    intro a b hab v hv
    cases v with
    | num d =>
      simp only [decide_eq_true_eq] at hv
      subst hv
      simp only [decide_eq_false_iff_not]
      exact hab
    | _ => exact Bool.noConfusion hv

/-! ## The two rules, derived — over a `List`, and that is the finding

`(literal-S)`'s payload is a `NEFinset String`; `Term.union`'s is a `List Term`. Going from one
to the other is `Finset.toList`, which is `Multiset.toList`, which is `Quotient.out` — and every
theorem stated through it picks up `Classical.choice`. The axiom scan says so: the first draft of
this file stated the two rules over `NEFinset` and five theorems came back unsanctioned.

So they are stated over a list with the two premises spelled out, which is choice-free and is the
honest shape of the claim. It is also the cost, and it is the argument *against* the absorption
that this file was written to find. See §11.5 of `docs/codec-audit.md`. -/

/-- **`(literal-S)` is derivable.** Every part of `Typed.literalS`'s conclusion — the held set and
    the member — comes from `Typed.literal` and `Typed.union`, with no premise `literalS` does not
    already have: `hnd` and `hne` are what `NEFinset` was carrying. -/
theorem typed_literalsS {l : List String} (hnd : l.Nodup) (hne : l ≠ []) :
    Typed (.union (l.map fun s => .literal (.str s)))
      (fun v => ∃ s, s ∈ l ∧ v = .str s) (some .S) := by
  have h := Typed.union (typedListμ_map_literal_str l) (dincomp_map_literal_str hnd)
  rw [hunion_map_literal_str, unanimous_map_const _ hne] at h
  exact h

/-- **`(literal-N)` is derivable**, on the same `ℓ ⊆ D` it already carries — not absorbed into a
    carrier, which §2.2 of the audit is the reason for. -/
theorem typed_literalsN {l : List Double} (hnd : l.Nodup) (hne : l ≠ [])
    (hD : ∀ d ∈ l, Numeral.WF d.toDec = true) :
    Typed (.union (l.map fun d => .literal (.num d)))
      (fun v => ∃ d, d ∈ l ∧ v = .num d) (some .N) := by
  have h := Typed.union (typedListμ_map_literal_num l hD) (dincomp_map_literal_num hnd)
  rw [hunion_map_literal_num, unanimous_map_const _ hne] at h
  exact h

/-! ## `tagsOf`, which I claimed would need a homogeneity proof

It does not. `tagsOfField` matches `.req (.literalS ls)` and hands back `ls.1`; the replacement
walks a union's options and unions what each contributes, and a non-conforming option contributes
`∅` — which is exactly what the existing `| _ => ∅` already does for every term that is not a
string literal. There is nothing to prove about the options being homogeneous, because
heterogeneity is not an error here, it is an empty contribution. A discriminator whose tags come
back `∅` fails `(dunion)`'s `htags` premise, which is where that error already belongs and where
it already lived.

Stated as a candidate and proved against the union form, so the claim is checked before the
definition it would replace is touched. -/

/-- The tag an option names, if it names one. Shallow, exactly as `tagsOfField` is: a term that
    is not a string literal contributes nothing, and that is not an error. -/
def tagOf1 : Term → Finset String
  | .literal (.str s) => {s}
  | _ => ∅

/-- The tags a discriminator field names — one level, no recursion, so no termination argument
    and no premise. -/
noncomputable def tagStringsOf : Term → Finset String
  | .union opts => (opts.map tagOf1).foldr (· ∪ ·) ∅
  | t => tagOf1 t

theorem mem_tagStringsOf_fold (l : List String) (x : String) :
    x ∈ (((l.map fun s => Term.literal (.str s)).map tagOf1).foldr (· ∪ ·) ∅) ↔ x ∈ l := by
  induction l with
  | nil => simp
  | cons s rest ih =>
    show x ∈ tagOf1 (Term.literal (.str s)) ∪
        ((rest.map fun s => Term.literal (.str s)).map tagOf1).foldr (· ∪ ·) ∅ ↔ _
    rw [Finset.mem_union, ih]
    show x ∈ ({s} : Finset String) ∨ x ∈ rest ↔ _
    rw [Finset.mem_singleton]
    exact List.mem_cons.symm

/-- **`tagsOf` recovers the tag set from the union form, with no premise** — the objection I
    raised in §11.4 of the audit and had not checked. A non-conforming option contributes `∅`,
    which is what `tagsOfField`'s existing `| _ => ∅` already does; heterogeneity is an empty
    contribution, not an error, and the error it *should* be is `(dunion)`'s `htags`. -/
theorem mem_tagStringsOf_union (l : List String) (x : String) :
    x ∈ tagStringsOf (.union (l.map fun s => .literal (.str s))) ↔ x ∈ l :=
  mem_tagStringsOf_fold l x

end Calculus
