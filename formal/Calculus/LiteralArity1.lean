import Calculus.Discharge

/-!
# The n-ary literal is derivable from singletons — the route not taken

`(literal)` is now one constructor, `literal (k : GroundKind) (ls : NEFinset k.Carrier)`, and it
absorbed `literalS` and `literalN`. **This file is why it is that shape and not a union.**

Before the collapse there were three constructors, and the obvious cheap fix was to keep only
arity one and let the n-ary form be `Term.union` over singletons — which `codec-formalization.md`
had proposed and which needs no new constructor at all. That fix works, and the theorems here are
the proof of it, restated over the collapsed constructor at singleton `ℓ`:

* `typed_literalsS` / `typed_literalsN` derive exactly what the old `Typed.literalS` and
  `Typed.literalN` concluded, from `Typed.literal` at a singleton and `Typed.union`. Same held
  set, same member.
* `dincomp_map_literal_str` / `_num` discharge §5's **(D)** from the alternatives being distinct.
* `uAtCan_map_literal_str` / `_num` discharge (U) **on both sides**, through
  `uniqueAdmission_of_sharedBase`.

The (U) one is worth stating plainly, because the §5 table used to say the opposite and was
wrong to. Read from the *pair*, two numeric options are refinements of one `numberCodec` at
disjoint predicates, which is all `uniqueAdmission_of_sharedBase` needs.
`uAtCan_of_literalN_disjoint` already made that argument for a union of n-ary numeric literals
and never used the n-ary constructor to make it — only the shared base — so it holds for
singletons too. The table now agrees (`sepA_literalN_disjoint`); the correction is recorded
below and it does not change a line of this file's proofs, which never appealed to the table.

**So why is the constructor n-ary?** Because the union route cannot carry `ℓ` as a `Finset`.
`Term.union` takes a `List Term`; bridging from a `NEFinset` is `Finset.toList`, which is
`Multiset.toList`, which is `Quotient.out` — `Classical.choice`. The first draft of this file was
stated over `NEFinset` and `#assert_axioms_all` rejected five theorems for exactly that. Stated
over `(l : List α)` with `l.Nodup` and `l ≠ []`, as it is here, it is choice-free — and those two
premises are precisely the gates the `℘⁺fin` repair had deleted. `Term` cannot have
`DecidableEq` either (`Term.custom` carries functions on `Value`), so `union` cannot take a
`NEFinset Term` and close the gap that way.

`docs/codec-audit.md` §11 records the whole comparison. What survives here is the part worth
keeping: whatever the collapsed rule concludes, these theorems say what it has to imply.
-/
namespace Calculus

/-- A singleton literal's held set, as the one-value predicate the options below are stated
    with. `HLit` is `∃ x ∈ ℓ, v = k.toValue x`; at a singleton that existential is the point. -/
theorem hLit_singleton_str (s : String) :
    HLit .string (.of s ∅) = fun v => v = Value.str s := by
  funext v; simp [HLit, NEFinset.of]

theorem hLit_singleton_num (d : WFDouble) :
    HLit .number (.of d ∅) = fun v => v = Value.num d.1 := by
  funext v; simp [HLit, NEFinset.of]

/-! ## The judgement

Stated over a bare `List` and applied to `Finset.toList`, rather than by induction on
`ls.1.toList` — the list is not a variable there, so the motive does not generalise. The same
shape the object-field work settled on. -/

/-- Every option of a string literal set is derivable, at `S`. No premise: `literalD` is `true`
    at every base but `number`. -/
theorem typedListμ_map_literal_str : ∀ (l : List String),
    TypedListμ (l.map fun s => .literal .string (.of s ∅))
      (l.map fun s => fun v => v = Value.str s)
      (l.map fun _ => some Member.S)
  | [] => .nil
  | s :: rest => by
      refine .cons ?_ (typedListμ_map_literal_str rest)
      show Typed (Term.literal .string (.of s ∅)) (fun v => v = Value.str s) (some .S)
      rw [← hLit_singleton_str s]
      exact Typed.literal .string (.of s ∅)

/-- …and of a numeric one, at `N`, **with no premise at all now**.

    This took `(∀ d ∈ l, Numeral.WF d.toDec = true)` and unpacked it one element at a time into
    `hD`, and its docstring said the premise "is not weakened and not absorbed: §2.2 of the
    audit is the reason that matters". It is absorbed, at JH's call: the list is a
    `List WFDouble` and each element carries its own gate. Nine lines of unpacking went with the
    premise — the clearest local measure of what typing the carrier bought. -/
theorem typedListμ_map_literal_num : ∀ (l : List WFDouble),
    TypedListμ (l.map fun d => .literal .number (.of d ∅))
      (l.map fun d => fun v => v = Value.num d.1)
      (l.map fun _ => some Member.N)
  | [] => .nil
  | d :: rest => by
      refine .cons ?_ (typedListμ_map_literal_num rest)
      show Typed (Term.literal .number (.of d ∅)) (fun v => v = Value.num d.1) (some .N)
      rw [← hLit_singleton_num d]
      exact Typed.literal .number (.of d ∅)

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
  refine ⟨fun h => hab ?_, fun h => hab ?_⟩
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
  refine ⟨fun h => hab ?_, fun h => hab ?_⟩
  · have h' : Value.num a.1 = Value.num b.1 := h (.num a.1) rfl
    exact Subtype.ext (by simpa using h')
  · have h' : Value.num b.1 = Value.num a.1 := h (.num b.1) rfl
    exact (Subtype.ext (by simpa using h') : b = a).symm

/-! ## (U) at the numeric base, and the claim that used to be made here

**What this section claimed.** That the read side of a numeric literal is `⊤` — the lemma was
called `admA_literalN_blind` — because the stored text goes through `Double.ofDec` and no
syntactic set of attributes bounds one value; and therefore that two numeric options "never
separate *in the table*" and separate only in the **pair**.

**Why the second half was false.** The premise is about *values*: no set of attributes names the
numerals that read into `ℓ`. `admA` never needed that. It needed to know whether an attribute is
admitted, and `ofDec` is a **function** — a stored numeral reads to at most one double, and one
double cannot inhabit two disjoint sets. Nothing about the answer had to be *nameable*, only
unique, and the row can obtain it by calling the codec rather than by describing it. Both of §5's
numeric `⊤`s came from the same confusion between "cannot bound which values" and "cannot bound
which option".

**What is true now.** `admALit`'s `.number` row is `((literalCodec .number ls).p ·).isSome`, and
`sepA_literalN_disjoint` separates two disjoint numeric literals in the table, alongside
`admA_literalN_sees`, which states exactly what an `N` attribute has to satisfy to be admitted.
The pair reading is not superseded: it is `uniqueAdmission_of_sharedBase`'s, it settles an
`n`-ary family and both sides in one step where the table settles a pair at a time, and it is the
one used below. Each is `numberCodec.restrict` at a predicate, the predicates are disjoint, and
that is the hypothesis. `uAtCan_of_literalN_disjoint` made this argument for a union of
`literalN`s — and never used the n-ary constructor for it, only the shared base, which is why it
holds here with `ℓ` as `Finset` data instead. -/

/-- (U) on both sides for a string literal set's options. -/
theorem uAtCan_map_literal_str {l : List String} (hnd : l.Nodup) :
    UAtCan (l.map fun s => .literal .string (.of s ∅)) := by
  show UniqueAdmission (semsOf _)
  have hs : semsOf (l.map fun s => .literal .string (.of s ∅))
      = (l.map fun s => literalCodec .string (.of s ∅)).map OptionSem.byAttempt := by
    simp [semsOf, List.map_map, specOf, optionSemOf, denote]
  rw [hs]
  refine uniqueAdmission_of_sharedBase (base := baseCodec .string)
    (qs := l.map fun s => inL .string (.of s ∅))
    (lawful_baseCodec .string).core ?_ ?_
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun s _ =>
      ⟨literalCodec_e_restrict .string (.of s ∅), literalCodec_p_restrict .string (.of s ∅)⟩
  · rw [List.pairwise_map]
    refine hnd.imp ?_
    intro a b hab v hv
    cases v <;> simp_all [inL, NEFinset.of]

/-- …and at the numeric base, by the same shared-base route: `n`-ary and both sides in one
    step, which is what this route buys over the table's pairwise `sepA_literalN_disjoint`. -/
theorem uAtCan_map_literal_num {l : List WFDouble} (hnd : l.Nodup) :
    UAtCan (l.map fun d => .literal .number (.of d ∅)) := by
  show UniqueAdmission (semsOf _)
  have hs : semsOf (l.map fun d => .literal .number (.of d ∅))
      = (l.map fun d => literalCodec .number (.of d ∅)).map OptionSem.byAttempt := by
    simp [semsOf, List.map_map, specOf, optionSemOf, denote]
  rw [hs]
  refine uniqueAdmission_of_sharedBase (base := baseCodec .number)
    (qs := l.map fun d => inL .number (.of d ∅))
    (lawful_baseCodec .number).core ?_ ?_
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun d _ =>
      ⟨literalCodec_e_restrict .number (.of d ∅), literalCodec_p_restrict .number (.of d ∅)⟩
  · rw [List.pairwise_map]
    refine hnd.imp ?_
    intro a b hab v hv
    cases v
    case num d =>
      -- the gate is `inL`'s now, on both the hypothesis and the goal
      cases hw : Numeral.WF d.toDec with
      | false => simp [inL, hw] at hv
      | true =>
        simp only [inL, hw, dite_true, NEFinset.of, Finset.mem_insert,
          Finset.not_mem_empty, or_false, decide_eq_true_eq] at hv
        simp only [inL, hw, dite_true, NEFinset.of, Finset.mem_insert,
          Finset.not_mem_empty, or_false, decide_eq_false_iff_not, hv]
        exact hab
    all_goals simp_all [inL, NEFinset.of]

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
    Typed (.union (l.map fun s => .literal .string (.of s ∅)))
      (fun v => ∃ s, s ∈ l ∧ v = .str s) (some .S) := by
  have h := Typed.union (typedListμ_map_literal_str l) (dincomp_map_literal_str hnd)
  rw [hunion_map_literal_str, unanimous_map_const _ hne] at h
  exact h

/-- **`(literal-N)` is derivable**, and the `ℓ ⊆ D` it used to carry is the list's element type.
    The docstring here said "not absorbed into a carrier, which §2.2 of the audit is the reason
    for"; it is absorbed, and §2.2's objection is answered in `Refutations.lean` instead, where
    the witness now lives on a transcription of §3's rule. -/
theorem typed_literalsN {l : List WFDouble} (hnd : l.Nodup) (hne : l ≠ []) :
    Typed (.union (l.map fun d => .literal .number (.of d ∅)))
      (fun v => ∃ d, d ∈ l ∧ v = .num d.1) (some .N) := by
  have h := Typed.union (typedListμ_map_literal_num l) (dincomp_map_literal_num hnd)
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
  | .literal .string ls => ls.1
  | _ => ∅

/-- The tags a discriminator field names — one level, no recursion, so no termination argument
    and no premise. -/
noncomputable def tagStringsOf : Term → Finset String
  | .union opts => (opts.map tagOf1).foldr (· ∪ ·) ∅
  | t => tagOf1 t

theorem mem_tagStringsOf_fold (l : List String) (x : String) :
    x ∈ (((l.map fun s => Term.literal .string (.of s ∅)).map tagOf1).foldr (· ∪ ·) ∅) ↔ x ∈ l := by
  induction l with
  | nil => simp
  | cons s rest ih =>
    show x ∈ tagOf1 (Term.literal .string (.of s ∅)) ∪
        ((rest.map fun s => Term.literal .string (.of s ∅)).map tagOf1).foldr (· ∪ ·) ∅ ↔ _
    rw [Finset.mem_union, ih]
    show x ∈ ({s} : Finset String) ∨ x ∈ rest ↔ _
    rw [Finset.mem_singleton]
    exact List.mem_cons.symm

/-- **`tagsOf` recovers the tag set from the union form, with no premise** — the objection I
    raised in §11.4 of the audit and had not checked. A non-conforming option contributes `∅`,
    which is what `tagsOfField`'s existing `| _ => ∅` already does; heterogeneity is an empty
    contribution, not an error, and the error it *should* be is `(dunion)`'s `htags`. -/
theorem mem_tagStringsOf_union (l : List String) (x : String) :
    x ∈ tagStringsOf (.union (l.map fun s => .literal .string (.of s ∅))) ↔ x ∈ l :=
  mem_tagStringsOf_fold l x

/-! ## The other route not taken: `literal` as a refinement

`refine(base, · ∈ ℓ)` is the second derivation of `literal`, and until now it cost precision:
`admA (.refine t q)` dropped `q`, so the refinement form was **blind on the read side** where
`admALit` was not. That was the argument against a literal API in which every primitive codec
accepts its own alternatives — `string('A')`, `number(1)`, `decimal('1')` — since the natural
encoding of that API is a refinement.

The argument is gone with the row. `admA` at a `refine` decodes with the base and applies `q`,
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

/-- **`literal k ℓ` and `refine(base k, ∈ ℓ)` denote the same pair**, up to the held set the
    literal carries — which `restrict` cannot know and `T` is not consulted by either row. -/
theorem denote_refine_ground_p (k : GroundKind) (ls : NEFinset k.Carrier) (a : Attr) :
    (denote (.refine (groundTerm k) (inL k ls))).p a = (denote (.literal k ls)).p a := by
  cases k <;> rfl

/-- **The question the row was changed to settle: yes.** `refine(base, ∈ ℓ)` is exactly as
    precise on the readable side as `literal base ℓ`, at every ground base — the numeric one
    included, where both rows ask the codec and get the same answer. A uniform
    `string('A')` / `number(1)` / `decimal('1')` API pays nothing for being uniform. -/
theorem admA_refine_ground_eq_admALit (k : GroundKind) (ls : NEFinset k.Carrier) (a : Attr) :
    admA (.refine (groundTerm k) (inL k ls)) a = admALit k ls a := by
  cases k
  case string => cases a <;> simp [admA, admALit, refineReads, groundTerm, denote,
                                   stringCodec, inL]
  case boolean => cases a <;> simp [admA, admALit, refineReads, groundTerm, denote,
                                    booleanCodec, inL]
  case binary => cases a <;> simp [admA, admALit, refineReads, groundTerm, denote,
                                   binaryCodec, inL]
  case null => cases a <;> simp [admA, admALit, refineReads, groundTerm, denote,
                                 nullCodec, inL]
  case decimal =>
    show (admA .decimal a && refineReads (groundTerm .decimal) (inL .decimal ls) a)
        = ((literalCodec .decimal ls).p a).isSome
    rw [show ((literalCodec .decimal ls).p a)
          = (decimalCodec.p a).bind (fun v => if inL .decimal ls v then some v else none) from rfl]
    show (admA .decimal a &&
        (match decimalCodec.p a with | some v => inL .decimal ls v | none => false)) = _
    cases h : decimalCodec.p a <;> cases a <;> simp_all [admA, decimalCodec]
    split <;> simp_all
  case number =>
    show (admA .number a && refineReads (groundTerm .number) (inL .number ls) a)
        = ((literalCodec .number ls).p a).isSome
    rw [show ((literalCodec .number ls).p a)
          = (numberCodec.p a).bind (fun v => if inL .number ls v then some v else none) from rfl]
    show (((numberCodec.p a).isSome : Bool) &&
        (match numberCodec.p a with | some v => inL .number ls v | none => false)) = _
    cases h : numberCodec.p a <;> simp [h]
    split <;> simp_all

/-- On the write side the refinement is **at least** as precise, and at `number` strictly:
    `adm (.literal .number ls)` is `inL` alone. -/
theorem adm_refine_ground_le_adm_literal (k : GroundKind) (ls : NEFinset k.Carrier)
    (v : Value) :
    adm (.refine (groundTerm k) (inL k ls)) v = true → adm (.literal k ls) v = true := by
  cases k <;> · intro h; rw [adm] at h; exact (Bool.and_eq_true _ _ ▸ h).2

/-- …and every base but `number` is an equality — for two different reasons, and the second
    is why `decimal` is worth a base of its own.

    At `string`, `boolean`, `binary` and `null` the base's own row is `⊤`, so the refinement adds
    nothing and the two coincide trivially. At `decimal` the row is *not* `⊤` — `isStored` gates
    it — and the equality holds anyway, because **membership in the alternatives implies the
    gate**: the carrier is `StoredNumeral`, so there is no alternative that fails `Stored`.

    That is exactly what fails at `number`. There the carrier is `Double` and §1's `D` is a
    predicate on its *text*, so `ls` may hold a double outside `D`, `inL` admits it and the
    base refuses it — which is why `adm (.literal .number ls)` over-approximates by precisely
    the conjunct `adm (.refine …)` carries. Typing the carrier is the whole difference. -/
theorem adm_refine_ground_eq_adm_literal (k : GroundKind) (ls : NEFinset k.Carrier)
    (v : Value) (hk : k ≠ .number) :
    adm (.refine (groundTerm k) (inL k ls)) v = adm (.literal k ls) v := by
  cases k
  case number => exact absurd rfl hk
  -- the gate is in the carrier, so `inL` already carries it
  case decimal =>
    cases v <;> simp only [adm, groundTerm, inL, isStored] <;> (try split) <;> simp_all
  all_goals simp [adm, groundTerm]

/-- The numeric row, written out: the refinement carries §1's `D` gate that the literal's row
    drops. -/
theorem adm_refine_ground_number (ls : NEFinset WFDouble) (v : Value) :
    adm (.refine (groundTerm .number) (inL .number ls)) v = (inD v && inL .number ls v) := rfl

end Calculus
