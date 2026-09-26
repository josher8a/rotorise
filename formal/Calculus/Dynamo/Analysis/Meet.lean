import Calculus.Lang.MeetV
import Calculus.Lang.MeetWrites
import Calculus.Lang.MeetA
import Calculus.Lang.MeetTyped
import Calculus.Dynamo.Lang.HeldSet
import Calculus.Dynamo.Lang.HeldFree
import Calculus.Dynamo.Analysis.Merge
import Calculus.Dynamo.Analysis.Orthogonality
import Calculus.Dynamo.Analysis.Laminar

/-!
# The meet

`Term.meet` is the intersection of two admissions, as a term. It is a derived function and not a
constructor: `some z` says a value satisfies `z` exactly when it satisfies both factors, `some
never` says nothing satisfies both, and `none` is a
refusal — the pair is one whose admission is a function rather than data, so no term states the
intersection. `held` refuses on that ground at every partner, `opaq`
refuses where its closed form cannot be compared with an exact held set, and `refine` refuses at a
`closure`. A pair that admits a common value and stores it at two members has no meet either, and
that is a refusal and not an empty one.

**The same on the read side, and `never` is the empty intersection of BOTH halves.** A pair
disjoint on one half only is not disjoint. `Orth1` tests the write occupancies and the read
occupancies. The two tests coincide below `opaque`, where `occA_le_occV` (under `HF`) makes a
pair disjoint on the write half disjoint on the read half too. `never` is for a pair disjoint on
both, and everything else refuses.

Among the ground and set terms no pair is disjoint on one half alone. The two halves part at a
`held`: `occV` of a `held` is its caller-side term's while `occA` of a `held` is its inner term's,
so an adapter and a native of the adapter's stored kind separate on the write half and not on the
read half.

**The write side agrees only where both factors name a member**, and that is weaker than "all three
write the same way". `μSyn` answers `none` for two different reasons — a term that writes no value
at all (`never`) and a term that names no *single* stored member (`union`, `opaq`, `mu`)
— so a factor answering `none` constrains nothing. The two examples at the foot of this
file are the witnesses: `union [string, null] ∧ null` is `null` and `opaq ∧ string` is `string`,
and in each the meet names a member neither shared with its `none`-answering factor.

The condition the rows keep reads off the MEET and not off the factors: where the meet names a
member, any member a factor names is that one, which is `meet_writes`. The other direction is
false and the two examples beside that theorem are why. A bottom names no member, so two factors
naming different members meet at a term that names none — `literal boolean ∧ string` is the
bottom, and `BOOL` and `S` never have to agree. The bottom is the whole of the reason, and it is
enough: a bottom names no member, so no pair whose meet is one can conclude anything about the
factors. The meet normalises a refinement over the bottom to the bottom, so that shape no longer
gives a second witness.

**The meet of a union is the union of the meets.** `Adm (.union os)` is `AdmAny os`, which admits
where one option admits, so the meet against a union is the meet against each option
(`Adm_meet_union`), with no certificate.

**The meet and the merge are two operations.** `Body.merge` (`Merge.lean`) joins two bodies over
*disjoint* names and is the record product: its held set is the product of the factors' held sets
through the split, and the map it admits is one neither factor admits. The meet intersects
admissions. `array(string) ∧ tuple(string 'a')` is `tuple(string 'a')` and is a meet;
`object {a} ⊗ object {b}` is `object {a, b}` and is a merge. The meet's object row does not call
`Body.merge`; each reads the two open blocks first, and that is the one place the two agree.

**An object's declared names meet by intersection, and only where both halves read the set the
same way.** `objAdmV` quantifies over the names the *value* carries and `AdmWild` is `none` where
the body declares no open block, so a closed object refuses an undeclared name on the value side:
the declared set is an upper bound. Two upper bounds meet at their intersection. The required names
unite, and **with both bodies closed** a required name outside the intersection makes the object
`never`, because that name must be present and the other factor refuses it. An *open* factor
refuses no name: its open block holds one the factor does not declare. So the open blocks are read
first, and one on either side answers the refusal before the required-name test is consulted.

The witness that the union of the declared names is wrong: `object {x : req string}` and
`object {y : req string}`, both closed, against the value `{x := "1", y := "2"}`. Each factor
refuses it, for the name the other declares. An object over the union of the two names admits it,
so the union rule answers `true` where both factors answer `false`.

**A shared name meets at the stronger core mark.** Both sides read the same presence fact.
`req` dominates `optional`, so each shared name has one of four two-mark meet rows. No slot
carries a reader. A closed body with an unshared required name meets at the bottom because one
factor requires the name and the other refuses it.

**The read side no longer parts from the write side at an undeclared name.** The read row used to
filter the stored names, and the filter at the old `drop` policy kept the declared names alone, so
such an object *skipped* an undeclared name rather than refusing it. The declared set then bounded
the read from below where it bounded the write from above, and a further guard carried the
condition under which the two halves agreed. That policy is gone. A body has one closed state, that
state refuses an undeclared name on both halves, and the filter, the guard and the pairs they
turned away go with the policy.
-/

namespace Calculus

open Alg (occV occA Orth1 occV_sound occA_sound occV_disjoint_of_Orth1 occA_disjoint_of_Orth1
  Term.isNever ObjectSlot.isReq Body.fields_mk Body.wild_mk Body.at_mk Body.block
  Body.slotAt Body.slotAt_pos Body.slotAt_neg listOf_cases HF_of_hasHeld alignPL_eq_rowOfG
  rowOfG_length rowOfG_none_eq rowOfG_some_eq rowOfG_mem forall₂_replicate forall₂_append
  forall₂_zip_append forall₂_zip_replicate forall₂_zip_take forall₂_zip_drop rowOfG_map
  rowOfG_forall₂ rowOfG_forall₂_left rowOfG_some_isSome rowOfG_total rowOfG_respread dominates_max
  listMeetRow_isList famList_isList allSome_map_forall₂ eq_never_of_isNever isReq_of_isBottom zipF_eq
  reqs_slotAt objObj_slots meetSRightL_eq meetSRight_union isReq_Field_meet meetSL_eq
  meet_union_of)

export Alg (ObjectSlot.isBottom Term.ofOptions allSome Term.refineOf Term.listOf Term.tupleOf zipF
  meetSRight meetSRightL famPrim hasHeld famSet famOpaq rowOfG dominates listMeetRow famList
  ObjectSlot.through objSlot ObjectSlot.isAbsentOpt objObj famObj Term.meet Term.meetSL Term.meetSTs
  ObjectSlot.meet Term.slotAt Term.optionAt Term.blockOf)


/-! ## Reading a field and a term -/

/-- Whether a predicate is data a term can carry through a meet. `closure` is the caller's own
    function and is the one case `Pred` keeps open. -/
def Pred.isData : Pred → Bool
  | .closure _ => false
  | _ => true

/-- One base's guard names one inhabitant. -/
theorem inL_inj {k : GroundKind} {x y : k.Carrier} {v : Value}
    (hx : inL k x v = true) (hy : inL k y v = true) : x = y := by
  cases k <;> cases v <;> simp_all [inL] <;>
    first
      | rfl
      | (obtain ⟨_, rfl⟩ := hx; obtain ⟨_, rfl⟩ := hy; rfl)

/-- A finite set with a positive count holds an element. `Finset.card_pos` states the same fact
    through a route to `Classical.choice` that the gateway baseline does not list. This case
    split on the underlying list reaches choice only through `Finset` membership. -/
theorem nonempty_of_card_pos {α : Type} {s : Finset α} (h : 0 < s.card) : s.Nonempty := by
  obtain ⟨⟨l⟩, _⟩ := s
  cases l with
  | nil => exact absurd h (Nat.lt_irrefl 0)
  | cons a _ => exact ⟨a, List.mem_cons_self⟩

/-- Two alternative sets over one base, met. `D6`: membership through `Finset.filter`, never
    `∩`, whose membership API is not a sanctioned route to `Classical.choice`. -/
def Pred.meetAlt (k : GroundKind) [DecidableEq k.Carrier]
    (A B : NEFinset k.Carrier) : Option (Option Pred) :=
  if h : 0 < (A.1.filter (fun x => x ∈ B.1)).card then
    some (some (.members k ⟨A.1.filter (fun x => x ∈ B.1), nonempty_of_card_pos h⟩))
  else some none

/-- An alternative set less another set over one base: the alternatives outside the second. -/
def Pred.minus (k : GroundKind) [DecidableEq k.Carrier]
    (A B : NEFinset k.Carrier) : Option (Option Pred) :=
  if h : 0 < (A.1.filter (fun x => x ∉ B.1)).card then
    some (some (.members k ⟨A.1.filter (fun x => x ∉ B.1), nonempty_of_card_pos h⟩))
  else some none

/-- Two exclusions over one base: the value is none of the alternatives of either set. -/
def Pred.excBoth (k : GroundKind) [DecidableEq k.Carrier]
    (A B : NEFinset k.Carrier) : Option (Option Pred) :=
  some (some (.except k ⟨A.1 ∪ B.1,
    match A.2 with | ⟨x, hx⟩ => ⟨x, Finset.mem_union.mpr (Or.inl hx)⟩⟩))

/-- **Two `members` predicates, met at any two bases.** `inL` at a base holds only a value of
    that base, so two different bases share no value. -/
def Pred.meetMem : (k : GroundKind) → NEFinset k.Carrier →
    (k' : GroundKind) → NEFinset k'.Carrier → Option (Option Pred)
  | .string,  A, .string,  B => Pred.meetAlt .string A B
  | .number,  A, .number,  B => Pred.meetAlt .number A B
  | .boolean, A, .boolean, B => Pred.meetAlt .boolean A B
  | .binary,  A, .binary,  B => Pred.meetAlt .binary A B
  | .null,    A, .null,    B => Pred.meetAlt .null A B
  | _, _, _, _ => some none

/-- A `members` predicate met with an `except` predicate, at any two bases. -/
def Pred.meetMemExc : (k : GroundKind) → NEFinset k.Carrier →
    (k' : GroundKind) → NEFinset k'.Carrier → Option (Option Pred)
  | .string,  A, .string,  B => Pred.minus .string A B
  | .number,  A, .number,  B => Pred.minus .number A B
  | .boolean, A, .boolean, B => Pred.minus .boolean A B
  | .binary,  A, .binary,  B => Pred.minus .binary A B
  | .null,    A, .null,    B => Pred.minus .null A B
  | _, _, _, _ => some none

/-- Two `except` predicates, met at any two bases. -/
def Pred.meetExc : (k : GroundKind) → NEFinset k.Carrier →
    (k' : GroundKind) → NEFinset k'.Carrier → Option (Option Pred)
  | .string,  A, .string,  B => Pred.excBoth .string A B
  | .number,  A, .number,  B => Pred.excBoth .number A B
  | .boolean, A, .boolean, B => Pred.excBoth .boolean A B
  | .binary,  A, .binary,  B => Pred.excBoth .binary A B
  | .null,    A, .null,    B => Pred.excBoth .null A B
  | _, _, _, _ => some none

/-- **Two predicates, met.** `none` is a refusal to combine, `some none` says that no value
    satisfies both, and `some (some r)` is the combined predicate. Every data case meets every
    data case: `members` and `except` at any two bases. A `closure` refuses, because nothing
    reads a caller's function. -/
def Pred.meetM : Pred → Pred → Option (Option Pred)
  | .members k A, .members k' B => Pred.meetMem k A k' B
  | .members k A, .except k' B  => Pred.meetMemExc k A k' B
  | .except k B,  .members k' A => Pred.meetMemExc k' A k B
  | .except k A,  .except k' B  => Pred.meetExc k A k' B
  | _, _ => none

/-- **An alternative shared by two sets is the only way both hold.** `inL` names one inhabitant
    per base, so a value that satisfies an alternative of each set satisfies one alternative
    lying in both. This is what makes the predicate meet exact rather than merely sound. -/
theorem exists_filter_iff {k : GroundKind} [DecidableEq k.Carrier]
    (A B : Finset k.Carrier) (v : Value) :
    (∃ x ∈ A.filter (fun x => x ∈ B), inL k x v = true)
      ↔ ((∃ x ∈ A, inL k x v = true) ∧ (∃ y ∈ B, inL k y v = true)) := by
  constructor
  · rintro ⟨x, hx, hv⟩
    obtain ⟨hxA, hxB⟩ := Finset.mem_filter.mp hx
    exact ⟨⟨x, hxA, hv⟩, ⟨x, hxB, hv⟩⟩
  · rintro ⟨⟨x, hxA, hxv⟩, ⟨y, hyB, hyv⟩⟩
    cases inL_inj hxv hyv
    exact ⟨x, Finset.mem_filter.mpr ⟨hxA, hyB⟩, hxv⟩

/-- The combined alternative set holds exactly where both sets hold. -/
theorem meetAlt_eval {k : GroundKind} [DecidableEq k.Carrier] {A B : NEFinset k.Carrier}
    {r : Pred} (h : Pred.meetAlt k A B = some (some r)) (v : Value) :
    Pred.eval r v = (inLs k A v && inLs k B v) := by
  unfold Pred.meetAlt at h
  split at h
  · injection h with h; injection h with h; subst h
    show inLs k _ v = _
    refine Bool.eq_iff_iff.mpr ?_
    simp only [inLs, Bool.and_eq_true, decide_eq_true_eq]
    exact exists_filter_iff A.1 B.1 v
  · exact absurd h (by simp)

/-- Where the two sets share no alternative, nothing satisfies both. -/
theorem meetAlt_empty {k : GroundKind} [DecidableEq k.Carrier] {A B : NEFinset k.Carrier}
    (h : Pred.meetAlt k A B = some none) (v : Value) :
    (inLs k A v && inLs k B v) = false := by
  unfold Pred.meetAlt at h
  split at h
  · exact absurd h (by simp)
  · rename_i hne
    have hne : A.1.filter (fun x => x ∈ B.1) = ∅ :=
      Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos hne)
    have hiff := exists_filter_iff A.1 B.1 v
    rw [hne] at hiff
    simp only [Finset.notMem_empty, false_and, exists_false, false_iff, not_and] at hiff
    cases hA : inLs k A v with
    | false => simp
    | true =>
        cases hB : inLs k B v with
        | false => simp
        | true =>
            simp only [inLs, decide_eq_true_eq] at hA hB
            exact absurd hB (hiff hA)

/-- **What a predicate meet must satisfy at each answer.** The combined predicate holds exactly
    where both hold, the empty answer holds where no value satisfies both, and a refusal asks
    nothing. -/
def MeetOk (q p : Pred) : Option (Option Pred) → Prop
  | some (some r) => ∀ v, Pred.eval r v = (Pred.eval q v && Pred.eval p v)
  | some none => ∀ v, (Pred.eval q v && Pred.eval p v) = false
  | none => True

/-- The obligation is symmetric in the two predicates. -/
theorem MeetOk.symm {q p : Pred} : ∀ {o : Option (Option Pred)}, MeetOk q p o → MeetOk p q o
  | some (some _), h => fun v => by rw [h v, Bool.and_comm]
  | some none, h => fun v => by rw [Bool.and_comm]; exact h v
  | none, _ => trivial

/-- Two alternative sets over one base meet as `meetAlt` says. -/
theorem meetAlt_ok (k : GroundKind) [DecidableEq k.Carrier] (A B : NEFinset k.Carrier) :
    MeetOk (.members k A) (.members k B) (Pred.meetAlt k A B) := by
  cases h : Pred.meetAlt k A B with
  | none => trivial
  | some o =>
    cases o with
    | none => exact fun v => meetAlt_empty h v
    | some r => exact fun v => meetAlt_eval h v

/-- An alternative that `inL` holds at a value names the value's base. -/
theorem inBase_of_inL {k : GroundKind} {x : k.Carrier} {v : Value} (h : inL k x v = true) :
    inBase k v = true := by
  cases k <;> cases v <;> simp_all [inL, inBase]

/-- A value outside a base satisfies no alternative at that base. -/
theorem inLs_false_of_base {k : GroundKind} {A : NEFinset k.Carrier} {v : Value}
    (h : inBase k v = false) : inLs k A v = false := by
  cases hA : inLs k A v with
  | false => rfl
  | true =>
    simp only [inLs, decide_eq_true_eq] at hA
    obtain ⟨x, _, hx⟩ := hA
    rw [inBase_of_inL hx] at h
    exact nomatch h

/-- Two different bases hold no common value. -/
theorem inBase_disj {k k' : GroundKind} (h : k ≠ k') (v : Value) :
    (inBase k v && inBase k' v) = false := by
  cases k <;> cases k' <;> cases v <;> first | rfl | exact absurd rfl h

/-- A literal and a base share the literal's values where the two bases agree, and no value
    elsewhere. -/
theorem inL_and_inBase {k k' : GroundKind} (x : k.Carrier) (v : Value) :
    (inL k x v && inBase k' v) = if k = k' then inL k x v else false := by
  split
  · next hk => subst hk; cases hl : inL k x v; rfl; rw [inBase_of_inL hl]; rfl
  · next hk =>
    cases hl : inL k x v; rfl
    have := inBase_disj hk v; rw [inBase_of_inL hl] at this; exact this

/-- `members` at two different bases share no value. -/
theorem memMem_none {k k' : GroundKind} (h : k ≠ k') (A : NEFinset k.Carrier)
    (B : NEFinset k'.Carrier) : MeetOk (.members k A) (.members k' B) (some none) := by
  intro v
  show (inLs k A v && inLs k' B v) = false
  have hd := inBase_disj h v
  cases hk : inBase k v with
  | false => rw [inLs_false_of_base hk]; rfl
  | true =>
    rw [hk, Bool.true_and] at hd
    rw [inLs_false_of_base hd, Bool.and_false]

/-- `members` and `except` at two different bases share no value. -/
theorem memExc_none {k k' : GroundKind} (h : k ≠ k') (A : NEFinset k.Carrier)
    (B : NEFinset k'.Carrier) : MeetOk (.members k A) (.except k' B) (some none) := by
  intro v
  show (inLs k A v && (inBase k' v && !inLs k' B v)) = false
  have hd := inBase_disj h v
  cases hk : inBase k v with
  | false => rw [inLs_false_of_base hk]; rfl
  | true =>
    rw [hk, Bool.true_and] at hd
    rw [hd, Bool.false_and, Bool.and_false]

/-- `except` at two different bases share no value. -/
theorem excExc_none {k k' : GroundKind} (h : k ≠ k') (A : NEFinset k.Carrier)
    (B : NEFinset k'.Carrier) : MeetOk (.except k A) (.except k' B) (some none) := by
  intro v
  show ((inBase k v && !inLs k A v) && (inBase k' v && !inLs k' B v)) = false
  have hd := inBase_disj h v
  cases hk : inBase k v with
  | false => rfl
  | true =>
    rw [hk, Bool.true_and] at hd
    rw [hd, Bool.false_and, Bool.and_false]

/-- **An alternative outside the second set is the only way the first holds and the second
    does not.** `inL` names one inhabitant per base, as in `exists_filter_iff`. -/
theorem exists_filter_not_iff {k : GroundKind} [DecidableEq k.Carrier]
    (A B : Finset k.Carrier) (v : Value) :
    (∃ x ∈ A.filter (fun x => x ∉ B), inL k x v = true)
      ↔ ((∃ x ∈ A, inL k x v = true) ∧ ¬ ∃ y ∈ B, inL k y v = true) := by
  constructor
  · rintro ⟨x, hx, hv⟩
    obtain ⟨hxA, hxB⟩ := Finset.mem_filter.mp hx
    refine ⟨⟨x, hxA, hv⟩, ?_⟩
    rintro ⟨y, hyB, hyv⟩
    cases inL_inj hv hyv
    exact hxB hyB
  · rintro ⟨⟨x, hxA, hxv⟩, hn⟩
    exact ⟨x, Finset.mem_filter.mpr ⟨hxA, fun hxB => hn ⟨x, hxB, hxv⟩⟩, hxv⟩

/-- An alternative set less another meets as a `members` against an `except`. -/
theorem minus_ok (k : GroundKind) [DecidableEq k.Carrier] (A B : NEFinset k.Carrier) :
    MeetOk (.members k A) (.except k B) (Pred.minus k A B) := by
  unfold Pred.minus
  split
  · intro v
    show inLs k _ v = (inLs k A v && (inBase k v && !inLs k B v))
    have hiff := exists_filter_not_iff A.1 B.1 v
    cases hA : inLs k A v with
    | false =>
      simp only [inLs, decide_eq_false_iff_not] at hA ⊢
      exact decide_eq_false (fun h => hA (hiff.mp h).1)
    | true =>
      have hA' : ∃ x ∈ A.1, inL k x v = true := by
        simpa only [inLs, decide_eq_true_eq] using hA
      obtain ⟨x, _, hxv⟩ := hA'
      rw [inBase_of_inL hxv]
      cases hB : inLs k B v with
      | true =>
        simp only [inLs, decide_eq_true_eq] at hB
        exact decide_eq_false (fun h => (hiff.mp h).2 hB)
      | false =>
        simp only [inLs, decide_eq_false_iff_not] at hB
        simp only [inLs, decide_eq_true_eq] at hA
        exact decide_eq_true (hiff.mpr ⟨hA, hB⟩)
  · rename_i hne
    have hne : A.1.filter (fun x => x ∉ B.1) = ∅ :=
      Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos hne)
    intro v
    show (inLs k A v && (inBase k v && !inLs k B v)) = false
    have hiff := exists_filter_not_iff A.1 B.1 v
    cases hA : inLs k A v with
    | false => rfl
    | true =>
      cases hB : inLs k B v with
      | true => simp
      | false =>
        simp only [inLs, decide_eq_true_eq, decide_eq_false_iff_not] at hA hB
        obtain ⟨x, hx, _⟩ := hiff.mpr ⟨hA, hB⟩
        rw [hne] at hx
        exact absurd hx (Finset.notMem_empty x)

/-- The alternatives of two sets over one base, as one set. -/
theorem inLs_union {k : GroundKind} [DecidableEq k.Carrier] (A B : NEFinset k.Carrier)
    (h : (A.1 ∪ B.1).Nonempty) (v : Value) :
    inLs k ⟨A.1 ∪ B.1, h⟩ v = (inLs k A v || inLs k B v) := by
  refine Bool.eq_iff_iff.mpr ?_
  simp only [inLs, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨x, hx, hv⟩
    rcases Finset.mem_union.mp hx with h | h
    · exact .inl ⟨x, h, hv⟩
    · exact .inr ⟨x, h, hv⟩
  · rintro (⟨x, h, hv⟩ | ⟨x, h, hv⟩)
    · exact ⟨x, Finset.mem_union.mpr (Or.inl h), hv⟩
    · exact ⟨x, Finset.mem_union.mpr (Or.inr h), hv⟩

/-- Two exclusions over one base meet as the exclusion of both sets. -/
theorem excBoth_ok (k : GroundKind) [DecidableEq k.Carrier] (A B : NEFinset k.Carrier) :
    MeetOk (.except k A) (.except k B) (Pred.excBoth k A B) := by
  intro v
  show (inBase k v && !inLs k ⟨A.1 ∪ B.1, _⟩ v)
    = ((inBase k v && !inLs k A v) && (inBase k v && !inLs k B v))
  rw [inLs_union]
  cases inBase k v <;> cases inLs k A v <;> cases inLs k B v <;> rfl

/-- `members` meets `members` at any two bases. -/
theorem meetMem_ok (k : GroundKind) (A : NEFinset k.Carrier) (k' : GroundKind)
    (B : NEFinset k'.Carrier) : MeetOk (.members k A) (.members k' B) (Pred.meetMem k A k' B) := by
  cases k <;> cases k' <;>
    first
      | exact meetAlt_ok _ A B
      | exact memMem_none (by decide) A B

/-- `members` meets `except` at any two bases. -/
theorem meetMemExc_ok (k : GroundKind) (A : NEFinset k.Carrier) (k' : GroundKind)
    (B : NEFinset k'.Carrier) :
    MeetOk (.members k A) (.except k' B) (Pred.meetMemExc k A k' B) := by
  cases k <;> cases k' <;>
    first
      | exact minus_ok _ A B
      | exact memExc_none (by decide) A B

/-- `except` meets `except` at any two bases. -/
theorem meetExc_ok (k : GroundKind) (A : NEFinset k.Carrier) (k' : GroundKind)
    (B : NEFinset k'.Carrier) :
    MeetOk (.except k A) (.except k' B) (Pred.meetExc k A k' B) := by
  cases k <;> cases k' <;>
    first
      | exact excBoth_ok _ A B
      | exact excExc_none (by decide) A B

/-- **The predicate meet is sound at every row.** -/
theorem meetM_ok : ∀ q p : Pred, MeetOk q p (Pred.meetM q p)
  | .members k A, .members k' B => meetMem_ok k A k' B
  | .members k A, .except k' B  => meetMemExc_ok k A k' B
  | .except k B,  .members k' A => (meetMemExc_ok k' A k B).symm
  | .except k A,  .except k' B  => meetExc_ok k A k' B
  | .members _ _, .closure _ => trivial
  | .except _ _,  .closure _ => trivial
  | .closure _, _ => trivial

/-- The combined predicate holds exactly where both hold. -/
theorem meetM_eval {q p r : Pred} (h : Pred.meetM q p = some (some r)) (v : Value) :
    Pred.eval r v = (Pred.eval q v && Pred.eval p v) := by
  have hok := meetM_ok q p
  rw [h] at hok
  exact hok v

/-- Where the meet is empty, nothing satisfies both. -/
theorem meetM_empty {q p : Pred} (h : Pred.meetM q p = some none) (v : Value) :
    (Pred.eval q v && Pred.eval p v) = false := by
  have hok := meetM_ok q p
  rw [h] at hok
  exact hok v


/-! ## The leaf meet of DynamoDB

The meet is `Alg.Term.meet`, the structural meet over a universe signature. DynamoDB supplies the
leaf meet `dynLeaf`: two primitives, a primitive and the top, and two predicates. -/

/-- Two literals: the same value at the same base, or `none` for the bottom. -/
def Ground.meetLit : (k : GroundKind) → k.Carrier → (k' : GroundKind) → k'.Carrier →
    Option Ground
  | .string, v, .string, v' => if v = v' then some (.literal .string v) else none
  | .boolean, v, .boolean, v' => if v = v' then some (.literal .boolean v) else none
  | .binary, v, .binary, v' => if v = v' then some (.literal .binary v) else none
  -- `Unit` has one inhabitant, so two null literals name the same value
  | .null, v, .null, _ => some (.literal .null v)
  | .number, v, .number, v' => if v = v' then some (.literal .number v) else none
  | _, _, _, _ => none

/-- **Two primitives met.** A base meets its own base and its own literals, and two literals meet
    at one value. Every other pair is the bottom. -/
def Ground.meet : Ground → Ground → Option Ground
  | .base k, .base k' => if k' = k then some (.base k) else none
  | .base k, .literal k' v => if k' = k then some (.literal k' v) else none
  | .literal k v, .base k' => if k' = k then some (.literal k v) else none
  | .literal k v, .literal k' v' => Ground.meetLit k v k' v'

/-- **A primitive met with the top.** A base is inside the top, so the pair meets at the base. A
    literal refuses: the closed form of the top is not compared with an exact held set. -/
def Ground.meetTop : Ground → Bool
  | .base _ => true
  | .literal _ _ => false

/-- **The leaf meet of DynamoDB.** -/
instance dynLeaf : Alg.Leaf dynSyn := ⟨Ground.meet, Ground.meetTop, Pred.isData, Pred.meetM⟩

/-- A closed traversal and a traversal through a block that admits nothing agree. -/
theorem objAdmV_none_never {α : Type} (fs : MapOf (α → Bool)) (keys : Finset Name)
    (g : {k // k ∈ keys} → α) :
    objAdmV fs none keys g = objAdmV fs (some (fun _ => false)) keys g := by
  unfold objAdmV
  exact decide_eq_decide.mpr (forall_congr' fun k => by unfold entryP; cases fs.at k.1 <;> exact Iff.rfl)


/-- **The closed body is the open body whose block is `never`**, on the write side. -/
theorem Adm_closed_eq_never_block (D : Finset Name) (f : {k // k ∈ D} → ObjectSlot) :
    Adm (.object (.mk D f none)) = Adm (.object (.mk D f (some .never))) := by
  funext v
  cases v with
  | map keys g =>
      show (valPresentT D f keys && objAdmV _ none keys g) =
        (valPresentT D f keys && objAdmV _ (some (fun _ => false)) keys g)
      rw [objAdmV_none_never]
  | _ => rfl

/-- …and on the read side. -/
theorem AdmA_closed_eq_never_block (D : Finset Name) (f : {k // k ∈ D} → ObjectSlot) :
    AdmA (.object (.mk D f none)) = AdmA (.object (.mk D f (some .never))) := by
  funext a
  cases a with
  | m keys g =>
      show (reqPresentT D f keys && objAdmV _ none keys g) =
        (reqPresentT D f keys && objAdmV _ (some (fun _ => false)) keys g)
      rw [objAdmV_none_never]
  | _ => rfl

/-! ## The union certificate

The certificate is defined here, after the meet, because two of its three tests are the meet. -/

/-- **Whether two terms meet at the bottom.** A pair that the meet cannot state answers `false`,
    so the pair is not certified. -/
def meetNever (x y : Term) : Bool := (Term.meet x y).any Term.isNever


mutual
/-- **The caller-side view**: each `held` becomes its caller-side term. The view admits each
    value that the term admits. The view of a `union` is the union of the views, because a union
    admits where one of its options admits. -/
def writeView : Term → Term
  | .held _ P _ _ => writeView P
  | .refine t p => .refine (writeView t) p
  | .list pre sp suf => .list (writeViewL pre) (writeViewO sp) (writeViewL suf)
  | .object b => .object (writeViewB b)
  | .union os => .union (writeViewL os)
  -- a set's view is the set of its element's view, where that view is held-free: the set row
  -- of `Adm` reads a held-free element element by element
  | .set t => if hasHeld (writeView t) then .set t else .set (writeView t)
  | t => t
def writeViewL : List Term → List Term
  | [] => []
  | t :: ts => writeView t :: writeViewL ts
def writeViewO : Option Term → Option Term
  | none => none
  | some t => some (writeView t)
def writeViewB : Body → Body
  | .mk fs f w => .mk fs (fun k => writeViewS (f k)) (writeViewO w)
def writeViewS : ObjectSlot → ObjectSlot
  | .req t => .req (writeView t)
  | .optional t => .optional (writeView t)
end

mutual
/-- **The stored-side view**: each `held` becomes its inner term. A `refine` above a `held`
    drops its predicate. Data exists only on the side where it was stated: the read test of the
    predicate decodes through `g`, so on the stored side the predicate is the closure `p ∘ g`,
    and the view keeps no closure. -/
def readView : Term → Term
  | .held t _ _ _ => readView t
  | .refine t p => if hasHeld t then readView t else .refine t p
  | .list pre sp suf => .list (readViewL pre) (readViewO sp) (readViewL suf)
  | .object b => .object (readViewB b)
  | .union os => .union (readViewL os)
  | .set t => if hasHeld (readView t) then .set t else .set (readView t)
  | t => t
def readViewL : List Term → List Term
  | [] => []
  | t :: ts => readView t :: readViewL ts
def readViewO : Option Term → Option Term
  | none => none
  | some t => some (readView t)
def readViewB : Body → Body
  | .mk fs f w => .mk fs (fun k => readViewS (f k)) (readViewO w)
def readViewS : ObjectSlot → ObjectSlot
  | .req t => .req (readView t)
  | .optional t => .optional (readView t)
end

/-- **The certificate through the two views of a `held`.** A `held` has two restrictions, and
    the meet sees neither: the meet refuses a `held`.
    The caller-side views answer the write question and the stored-side views answer the read
    question. Each view is held-free, so the meet answers both. The test runs only where a
    `held` occurs. -/
def certViews (x y : Term) : Bool :=
  (hasHeld x || hasHeld y)
    && meetNever (writeView x) (writeView y) && meetNever (readView x) (readView y)

/-- **The certificate for one pair of options**: the meet, of the two terms or of their two
    views, or the slot test. A `held` reaches the meet only through its views, so `certViews` is
    the second disjunct.

    **The slot test is the third disjunct, because the meet refuses a closure.** A `refine` at a
    `closure` has an admission that is a function, so the meet answers `none` beside every term
    but the bottom. The occupancies read no predicate: `refine string (closure q)` beside
    `list [] (some number) []` writes `str` against `list` and reads `S` against `L`, so
    `Orth1` separates the pair where the meet cannot state the pair. -/
def certPair (x y : Term) : Bool := meetNever x y || certViews x y || Orth1 x y

/-- The certificate over a list of options, pair by pair. -/
def certAll : List Term → Bool
  | [] => true
  | t :: ts => ts.all (fun u => certPair t u) && certAll ts

/-- **The certificate a union must carry for its admission to be the join of its options'.**
    One condition. Each pair of options is certified, so no value and no attribute has two
    admitters, and nothing is refused for being admitted twice.

    An open object needs no second condition. The structural lemmas carry the open block
    themselves, so a union holding an open block certifies on separation alone. -/
def unionOk (os : List Term) : Bool :=
  certAll os

/-- The certificate, in the pairwise form. -/
theorem pairwise_of_certAll : ∀ {ts : List Term}, certAll ts = true →
    List.Pairwise (fun x y => certPair x y = true) ts
  | [], _ => .nil
  | _ :: _, h => by
      simp only [certAll, Bool.and_eq_true, List.all_eq_true] at h
      exact .cons (fun u hu => h.1 u hu) (pairwise_of_certAll h.2)

/-- Required presence dominates optional presence. -/
example : ObjectSlot.meet (ObjectSlot.optional .string) (ObjectSlot.req .string)
    = some (ObjectSlot.req .string) := by rfl

/-- Required slots meet without comparing values outside their carried terms. -/
example : ObjectSlot.meet (ObjectSlot.req .string) (ObjectSlot.req .string)
    = some (ObjectSlot.req .string) := by rfl

/-! ## What the rows answer

Worked pairs, one per class, checked by the equation compiler rather than described. The first is
the example the meet exists for: an array admits every length and a tuple pins one, so the meet is
the tuple. -/

example : Term.meet (Term.array .string) (Term.tuple [.literal .string "a"] none)
    = some (Term.tuple [.literal .string "a"] none) := by rfl

/-- Two value kinds that never meet. -/
example : Term.meet Term.string Term.number = some Term.never := by rfl

/-- A literal against its own base is the literal: the finer of the two. -/
example : Term.meet (Term.literal .string "a") Term.string
    = some (Term.literal .string "a") := by rfl

/-- …and against another value of the same base, nothing. -/
example : Term.meet (Term.literal .string "a") (Term.literal .string "b")
    = some Term.never := by rfl

/-- A literal at a base that shares nothing with the partner is still the bottom. -/
example : Term.meet (Term.literal .string "1") Term.boolean = some Term.never := by rfl

/-- **The null point needs no row of its own.** A null point is the null term joined by a union,
    so the union rows distribute over it and the ground rows answer each cell. This is the pair
    that had a row and got it wrong: the wrapper this replaced dropped the point at every
    partner but another wrapper and a `null`, and `opaq` holds the point. -/
example : Term.meet (Term.union [.string, .null]) Term.opaq
    = some (Term.union [.string, .null]) := by rfl

/-- …and against the null term alone the string cell is the bottom, so one option survives. -/
example : Term.meet (Term.union [.string, .null]) Term.null = some Term.null := by rfl

/-- **Two open factors meet pointwise.** The left body requires `x` and the right does not
    declare it, so `x` meets the right body's open block and stays required. `y` meets the left
    body's block and stays optional, and the blocks meet to `string`. The two examples below are
    a value both admit, which the meet admits too. -/
example :
    (Term.meet
        (Term.object (.mk {"x"} (fun _ => .req .string) (some .string)))
        (Term.object (.mk {"y"} (fun _ => .optional .string) (some .string)))).map
      (fun z => match z with
        | .object b => (decide ("x" ∈ b.fields), decide ("y" ∈ b.fields), b.wild.isSome)
        | _ => (false, false, false))
      = some (true, true, true) := by rfl

/-- The left body admits `{x := "1"}` through its declared slot… -/
example : Adm (.object (.mk {"x"} (fun _ => .req .string) (some .string)))
    (.map {"x"} (fun _ => .str "1")) = true := by
  simp [Adm_rows, valPresentT, objAdmV, entryP, MapOf.at, inBase]

/-- …and the right body admits it through its open block, at a name it does not declare. -/
example : Adm (.object (.mk {"y"} (fun _ => .optional .string) (some .string)))
    (.map {"x"} (fun _ => .str "1")) = true := by
  simp [Adm_rows, valPresentT, objAdmV, entryP, MapOf.at]
  apply decide_eq_true
  intro k
  rw [if_neg (by have hk := k.2; simp only [Finset.mem_singleton] at hk; simp [hk])]
  rfl

/-! ### The presence table

Four two-mark cells. Required presence dominates optional presence, and each cell meets the
carried terms. -/

/-- The four two-mark rows reduce in the kernel. -/
example : ObjectSlot.meet (ObjectSlot.req .string) (ObjectSlot.optional .string)
    = some (ObjectSlot.req .string) := by rfl
example : ObjectSlot.meet (ObjectSlot.optional .string) (ObjectSlot.req .string)
    = some (ObjectSlot.req .string) := by rfl
example : ObjectSlot.meet (ObjectSlot.optional .string) (ObjectSlot.optional .string) =
    some (ObjectSlot.optional .string) := by rfl

/-- A `req` slot over the bottom is still the bottom and not a refusal: both halves force the
    name present, so both agree that nothing satisfies the object. -/
example : ObjectSlot.meet (ObjectSlot.req .string) (ObjectSlot.req .boolean)
    = some (ObjectSlot.req .never) := by rfl



/-- **Two closed factors with no shared name meet at the closed body with no name.** Each name
    meets the other body's default `never` at `optional never`, which is the default itself, so
    the normal form drops the name. -/
example :
    (Term.meet
        (Term.object (.mk {"x"} (fun _ => .optional .string) none))
        (Term.object (.mk {"y"} (fun _ => .optional .string) none))).map
      (fun z => match z with
        | .object b => (decide ("x" ∈ b.fields), decide ("y" ∈ b.fields), b.wild.isSome)
        | _ => (true, true, true))
      = some (false, false, false) := by rfl

/-- **Two objects that declare one name with one mark and no literal are certified**: the
    required slot meets `string` with `boolean` at the bottom. -/
example : unionOk [.object (.mk {"a"} (fun _ => .req .string) none),
    .object (.mk {"a"} (fun _ => .req .boolean) none)] = true := by decide

/-! ### The bottom bubbles up through a required slot

A slot that must hold a value passes the bottom up; a slot that may be empty stops it. So the
meet's output is normal, and `Term.isNever` is the whole of the union guard's filter again. -/

/-- A tuple's declared position is such a slot… -/
example : Term.meet (Term.tuple [.string] none) (Term.tuple [.boolean] none)
    = some Term.never := by rfl

/-- …an `array`'s element is not, because an array over the bottom holds the empty list. -/
example : Term.meet (Term.array .string) (Term.array .boolean) = some (Term.array .never) := by rfl

/-- A refinement's inner term is such a slot, and this is the pair that made a union of empty
    options: each option met the partner at a refinement over the bottom, which the filter could
    not see. Both options now answer the bottom and the filter drops them. -/
example : Term.meet
    (Term.refine .string (.members .string ⟨{"1"}, Finset.singleton_nonempty _⟩)) Term.null
      = some .never := by rfl

example : unionOk [.object (.mk {"x"} (fun _ => .optional .string) none)] = true := by
  simp [unionOk, certAll]

example : unionOk [.object (.mk {"x"} (fun _ => .req .string) none)]
    = true := by
  simp [unionOk, certAll]

/-- …and a singleton union of an **open** object is certified: a union of one option has no
    pair to certify. -/
example : unionOk [.object (.mk {"a"} (fun _ => .req .string) (some .string))]
    = true := by
  simp [unionOk, certAll]

/-! ### Arrays told apart by a literal position

The owner's witness. Each list below starts with a literal, and the empty list is an option of
its own. Each pair meets at the bottom. -/

/-- The three options: a nonempty list of `"A"`, a nonempty list of `"B"`, and the empty list. -/
def literalListOptions : List Term :=
  [.list [.literal .string "A"] (some (.literal .string "A")) [],
   .list [.literal .string "B"] (some (.literal .string "B")) [],
   .list [] none []]

/-- **The meet certifies the union**: each pair meets at the bottom. -/
theorem unionOk_literalListOptions : unionOk literalListOptions = true := by decide

/-- **The crossing control is not certified.** `array (literal "A")` and `array (literal "B")`
    both hold `[]`, so the meet is `array never`, which holds `[]` and is not the bottom. -/
theorem not_unionOk_literalArrays :
    unionOk [.array (.literal .string "A"), .array (.literal .string "B")] = false := by decide

/-! ### Two restricted sets, met at their elements

The meet certifies two string sets whose members are disjoint, because the elements meet at the
bottom and no set is empty. -/

/-- **Two string sets with disjoint members meet at the bottom.** -/
theorem meetNever_disjointStringSets :
    meetNever (.set (.refine .string (.members .string (NEFinset.of "a" {"b"}))))
      (.set (.refine .string (.members .string (NEFinset.of "c" ∅)))) = true := by
  decide

/-- **Two string sets that share a member meet at the set of the shared members.** -/
theorem meet_stringSets_shared :
    Term.meet (Term.set (.refine .string (.members .string (NEFinset.of "a" {"b"}))))
      (Term.set (.refine .string (.members .string (NEFinset.of "b" {"c"}))))
      = some (Term.set (.refine .string (.members .string (NEFinset.of "b" ∅)))) := by
  rfl

/-! ### The views certify a `held` whose caller side is precise

A string set held as a list of strings, beside a list of numbers. Both terms write the kind of a
list, so the occupancies meet. The caller-side views meet at the bottom when the caller side
requires one element or more, and the stored-side views differ in kind. -/

/-- The meet of the two terms does not certify the pair. -/
theorem certPair_heldNE_base :
    meetNever (.held (.set .string) (.list [.string] (some .string) []) id id)
        (.list [] (some .number) []) = false := by
  decide

/-- **A caller side that requires one element or more is certified** beside a list of numbers. -/
theorem certPair_heldNE :
    certPair (.held (.set .string) (.list [.string] (some .string) []) id id)
      (.list [] (some .number) []) = true := by
  decide

/-- **A caller side that admits the empty list is refused**, because the list of numbers admits
    the empty list too. -/
theorem certPair_heldAny :
    certPair (.held (.set .string) (.list [] (some .string) []) id id)
      (.list [] (some .number) []) = false := by
  decide

/-! ### Why the write-agreement condition is conditional

Two meets that are not the bottom and whose factor names no member. They are why the condition the
rows keep is "where both factors name a member" rather than "all three name the same member": a
`μSyn` of `none` is a term that names no single stored member, not a term that writes nothing. -/

example : μSyn (Term.union [.string, .null]) = none := by simp [μSyn_rows, unanimous]

example : ¬ (μSyn Term.null = μSyn (Term.union [.string, .null])) := by
  simp [μSyn_rows, unanimous]

example : Term.meet Term.opaq Term.string = some Term.string := by rfl

/-- `held` still refuses, and the ground is its alone: it carries host
    functions (`Term.lean`), so no term states the intersection of two of them. -/
example : Term.meet (Term.held .string .opaq (fun v => v) (fun v => v)) Term.string = none := by rfl

example : ¬ (μSyn Term.string = μSyn Term.opaq) := by simp [μSyn_rows]

/-! ## The homomorphism

`Adm` carries the meet to conjunction. `Alg.Adm_meet` proves the homomorphism once, over any
signature, and recurses as the meet does. The rows below are the DynamoDB facts that its laws
read.
-/


/-! ## The levers -/

/-! ## What `opaque` admits

`Adm .opaq v` is `dom(e)` of `Ω`, and a scalar's budget is one layer, so each row below
reduces by `rfl`. -/

/-- `opaque` writes every string, so `string` is the finer term. -/
theorem Adm_opaq_str (s : String) : Adm .opaq (.str s) = true := rfl

/-- …every boolean. -/
theorem Adm_opaq_bool (b : Bool) : Adm .opaq (.bool b) = true := rfl

/-- …every byte string. -/
theorem Adm_opaq_bin (b : Bytes) : Adm .opaq (.bin b) = true := rfl

/-- …and the null point. -/
theorem Adm_opaq_null : Adm .opaq .null = true := rfl

/-- …and every numeral, exactly on `D`. -/
theorem Adm_opaq_num (d : WFNumeral) :
    Adm .opaq (.num d) = inD (.num d) := by
  rw [show Adm .opaq (.num d) = true from rfl]
  simp [inD]


/-! ## DynamoDB is an instance of the meet laws, on the write side

`Alg.Adm_meet` proves the homomorphism once, over any signature. DynamoDB supplies the laws of its
formers (`dynFormerAdm`) and of its leaf meet (`dynLeafAdm`). A primitive law is a fact about
`inBase` and `inL`, and a set law is a fact about `setCodec`. The disjointness of two formers is
a theorem of the shape classes (`dynShapes`). -/

/-- `opaque`'s row is `dom(e)` of its codec. -/
theorem Adm_opaq_eq (v : Value) : Adm .opaq v = (Ω.e v).isSome := rfl

/-- **`ofOptions` admits what its options admit**, and no certificate is spent. -/
theorem Adm_ofOptions (ts : List Term) (v : Value) :
    Adm (Term.ofOptions ts) v = AdmAny ts v := by
  match ts with
  | [] => rfl
  | [t] => simp only [Term.ofOptions, AdmAny_cons, AdmAny_nil, Bool.or_false]
  | _ :: _ :: _ => rfl

/-- **Two sets whose elements share no value share no set**, because no set is empty. -/
theorem Adm_set_and_false {a y : Term} (h : ∀ u, (Adm a u && Adm y u) = false) (v : Value) :
    (Adm (.set a) v && Adm (.set y) v) = false := by
  cases hA : Adm (.set a) v with
  | false => rfl
  | true =>
  cases hY : Adm (.set y) v with
  | false => rfl
  | true =>
  exfalso
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hA
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hY
  have hne : ∀ w, ((denote a).e w).isSome = true → ((denote y).e w).isSome = true → False :=
    fun w h1 h2 => by
      have := h w
      rw [(Adm_exact a w).mpr h1, (Adm_exact y w).mpr h2] at this
      exact Bool.noConfusion this
  rcases setCodec_e_eq.mp hp with ⟨S, rfl, hS⟩ | ⟨S, rfl, hS⟩ | ⟨S, rfl, hS⟩ <;>
    obtain ⟨x, hx⟩ := S.2
  · exact hne _ (encSet_elem hS x hx) (encSet_elem (c := denote y) (inj := Value.str) hq x hx)
  · exact hne _ (encSet_elem hS x hx) (encSet_elem (c := denote y) (inj := Value.num) hq x hx)
  · exact hne _ (encSet_elem hS x hx) (encSet_elem (c := denote y) (inj := Value.bin) hq x hx)

/-- **Over held-free terms, the set of the element meet is the meet of the sets.** Each set
    writes exactly where every element does (`setCodec_e_isSome_of_sub`), so the element
    equation lifts. -/
theorem Adm_set_meet {a y z : Term} (ha : HF a) (hy : HF y) (hz : HF z)
    (h : ∀ u, Adm z u = (Adm a u && Adm y u)) (v : Value) :
    Adm (.set z) v = (Adm (.set a) v && Adm (.set y) v) := by
  have hr : ∀ t, HF t → ∀ w, ((denote t).e w).isSome = Adm t w := fun t _ w =>
    isSome_e_eq_Adm (Adm_exact t) w
  apply Bool.eq_iff_iff.mpr
  rw [Bool.and_eq_true]
  show ((setCodec (denote z)).e v).isSome = true ↔
    ((setCodec (denote a)).e v).isSome = true ∧ ((setCodec (denote y)).e v).isSome = true
  rw [setCodec_e_isSome_of_sub (sub_denote z hz), setCodec_e_isSome_of_sub (sub_denote a ha),
    setCodec_e_isSome_of_sub (sub_denote y hy)]
  cases v <;> simp only [hr z hz, hr a ha, hr y hy, h, Bool.and_eq_true, and_false, iff_self] <;>
    exact ⟨fun H => ⟨fun x hx => (H x hx).1, fun x hx => (H x hx).2⟩,
      fun H x hx => ⟨H.1 x hx, H.2 x hx⟩⟩

/-- The right operands `meetSRight` hands to a family: everything its own rows do not answer. -/
def Delegated : Term → Prop
  | .never | .held _ _ _ _ | .refine _ _ | .union _ | .var _ | .mu _ => False
  | _ => True

/-- **Two primitives met at a primitive admit what both admit.** -/
theorem Adm_prim_some : ∀ g g' h : Ground, Ground.meet g g' = some h →
    ∀ v, Adm (.prim h) v = (Adm (.prim g) v && Adm (.prim g') v)
  | .base k, .base k', h, hp, v => by
      simp only [Ground.meet] at hp
      split at hp
      · next hk => simp only [Option.some.injEq] at hp; subst hp hk; exact (Bool.and_self _).symm
      · exact nomatch hp
  | .base k, .literal k' x, h, hp, v => by
      simp only [Ground.meet] at hp
      split at hp
      · next hk =>
          simp only [Option.some.injEq] at hp; subst hp
          rw [Bool.and_comm]; exact ((inL_and_inBase x v).trans (if_pos hk)).symm
      · exact nomatch hp
  | .literal k x, .base k', h, hp, v => by
      simp only [Ground.meet] at hp
      split at hp
      · next hk =>
          simp only [Option.some.injEq] at hp; subst hp
          exact ((inL_and_inBase x v).trans (if_pos hk.symm)).symm
      · exact nomatch hp
  | .literal k x, .literal k' x', h, hp, v => by
      simp only [Ground.meet] at hp
      cases k <;> cases k' <;> simp only [Ground.meetLit, reduceCtorEq] at hp <;>
        (try split at hp) <;>
        first
          | (simp only [reduceCtorEq] at hp)
          | (simp only [Option.some.injEq] at hp
             subst hp
             cases v <;> simp_all [Adm_rows, AdmLit, inL])

/-- **Two primitives met at the bottom share no value.** -/
theorem Adm_prim_none : ∀ g g' : Ground, Ground.meet g g' = none →
    ∀ v, (Adm (.prim g) v && Adm (.prim g') v) = false
  | .base k, .base k', hp, v => by
      simp only [Ground.meet] at hp
      split at hp
      · exact nomatch hp
      · next hk => exact inBase_disj (Ne.symm hk) v
  | .base k, .literal k' x, hp, v => by
      simp only [Ground.meet] at hp
      split at hp
      · exact nomatch hp
      · next hk => rw [Bool.and_comm]; exact (inL_and_inBase x v).trans (if_neg hk)
  | .literal k x, .base k', hp, v => by
      simp only [Ground.meet] at hp
      split at hp
      · exact nomatch hp
      · next hk => exact (inL_and_inBase x v).trans (if_neg (Ne.symm hk))
  | .literal k x, .literal k' x', hp, v => by
      simp only [Ground.meet] at hp
      cases k <;> cases k' <;> simp only [Ground.meetLit, reduceCtorEq] at hp <;>
        (try split at hp) <;>
        (try (simp only [reduceCtorEq] at hp)) <;>
        (cases v <;> simp_all [Adm_rows, AdmLit, inL])

/-- **A base is inside the top.** -/
theorem Adm_prim_top : ∀ g : Ground, Ground.meetTop g = true →
    ∀ v, Adm (.prim g) v = true → Adm .opaq v = true
  | .base k, _, v, hv => by
      have e : Adm (.base k) v = (Adm (.base k) v && Adm .opaq v) := by cases k <;> cases v <;> rfl
      rw [hv, Bool.true_and] at e
      exact e.symm
  | .literal _ _, h, _, _ => by simp [Ground.meetTop] at h

/-- The former class of a value: its root constructor. -/
def Value.former : Value → Alg.Former
  | .str _ | .num _ | .bool _ | .bin _ | .null => .prim
  | .strSet _ | .numSet _ | .binSet _ => .set
  | .arr _ => .list
  | .map _ _ => .object

/-- The former class of an attribute: its root constructor. -/
def Attr.former : Attr → Alg.Former
  | .s _ | .n _ | .b _ | .bool _ | .null => .prim
  | .ss _ | .ns _ | .bs _ => .set
  | .l _ => .list
  | .m _ _ => .object

/-- **The shape classes of DynamoDB.** A base or a literal writes and reads a scalar, `setCodec`
    writes and reads one of the three sets, and the prisms build `arr`, `l`, `map` and `m`. -/
noncomputable instance dynShapes : Alg.Shapes dynSyn where
  former := Value.former
  formerA := Attr.former
  prim g v h := by
    have h' := (Alg.PrimAdm.admV_exact (S := dynSyn) g v).mpr h
    cases g with
    | base k => cases k <;> cases v <;> first | rfl | exact nomatch h'
    | literal k x =>
        cases k <;> cases v <;> first | rfl | simp [Alg.PrimAdm.admV, AdmLit, inL] at h'
  primA g a h := by
    have h' := (Alg.PrimAdmA.admA_exact (S := dynSyn) g a).mpr h
    cases g with
    | base k => cases k <;> cases a <;> first | rfl | exact nomatch h'
    | literal k x => cases k <;> cases a <;> first | rfl | exact nomatch h'
  set L hL c v h := by
    cases hL
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp h
    rcases setCodec_e_eq.mp ha with ⟨S, rfl, -⟩ | ⟨S, rfl, -⟩ | ⟨S, rfl, -⟩ <;> rfl
  setA L hL c a h := by
    cases hL
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h
    rcases setCodec_p_eq.mp hw with ⟨S, rfl, -⟩ | ⟨S, rfl, -⟩ | ⟨S, rfl, -⟩ <;> rfl
  list L hL _ := by cases hL; rfl
  listA L hL _ := by cases hL; rfl
  map F hF _ := by cases hF; rfl
  mapA F hF _ := by cases hF; rfl

/-- The formers of DynamoDB: the set laws of `setCodec`. -/
instance dynFormerAdm : Alg.FormerAdm dynSyn where
  set_meet _ _ _ ha hy hz h v := Adm_set_meet ha hy hz h v
  set_never _ _ h v := Adm_set_and_false h v

/-- The leaf meet of DynamoDB is exact on the write side. -/
instance dynLeafAdm : Alg.LeafAdm dynSyn where
  prim_some g g' h hp v := Adm_prim_some g g' h hp v
  prim_none g g' hp v := Adm_prim_none g g' hp v
  prim_top g hg v hv := Adm_prim_top g hg v hv
  pmeet_some _ _ _ h v := meetM_eval h v
  pmeet_none _ _ h v := meetM_empty h v

/-- **`Adm` is a homomorphism from the meet to conjunction.** Where two terms have a meet,
    the values it admits are exactly the values both admit. `Alg.Adm_meet` at DynamoDB. -/
theorem Adm_meet (x y : Term) (z : Term) (h : Term.meet x y = some z) (v : Value) :
    Adm z v = (Adm x v && Adm y v) :=
  Alg.Adm_meet x y z h v

/-! ## The member the meet names

`Alg.meet_writes` proves the member law once, over any signature. DynamoDB supplies the law of its
leaf meet: every primitive of a base names that base's member, and two primitives meet only at one
base. -/

/-- **Two primitives meet only at one base**, so the met primitive names the member of each. -/
theorem Ground.meet_groundμ : ∀ g g' h : Ground, Ground.meet g g' = some h →
    Alg.Sem.groundμ (S := dynSyn) h = Alg.Sem.groundμ (S := dynSyn) g ∧
      Alg.Sem.groundμ (S := dynSyn) h = Alg.Sem.groundμ (S := dynSyn) g'
  | .base k, .base k', h, hp => by
      simp only [Ground.meet] at hp
      split at hp
      · next hk => cases hp; subst hk; exact ⟨rfl, rfl⟩
      · exact nomatch hp
  | .base k, .literal k' x, h, hp => by
      simp only [Ground.meet] at hp
      split at hp
      · next hk => cases hp; subst hk; exact ⟨rfl, rfl⟩
      · exact nomatch hp
  | .literal k x, .base k', h, hp => by
      simp only [Ground.meet] at hp
      split at hp
      · next hk => cases hp; subst hk; exact ⟨rfl, rfl⟩
      · exact nomatch hp
  | .literal k x, .literal k' x', h, hp => by
      simp only [Ground.meet] at hp
      cases k <;> cases k' <;> simp only [Ground.meetLit, reduceCtorEq] at hp <;>
        (try split at hp) <;>
        first
          | (simp only [reduceCtorEq] at hp)
          | (cases hp; exact ⟨rfl, rfl⟩)

/-- **The member law of the DynamoDB leaf meet.** -/
instance dynLeafWrites : Alg.LeafWrites dynSyn where
  prim_μ g g' h hp m hm := by
    obtain ⟨h1, h2⟩ := Ground.meet_groundμ g g' h hp
    exact ⟨fun mx hx => Option.some.inj ((h1.trans hx).symm.trans hm),
      fun my hy => Option.some.inj ((h2.trans hy).symm.trans hm)⟩


/-- **The converse is false, and a bottom is why.** Two factors naming different members meet at
    the bottom, which names none, so a theorem concluding `mx = my` from the factors alone fails
    here. -/
example : Term.meet (Term.literal .boolean true) Term.string = some Term.never := by rfl

example : μSyn Term.never = none := rfl

/-- The refinement that used to be the second witness is now the bottom, because the meet
    normalises: a refinement over the bottom holds nothing, so `Term.refineOf` answers the bottom.
    The hypothesis form is still the right one — the first witness needs no wrapper — and this
    example is kept because it pins the normalisation at the row that motivated it. -/
example : Term.meet (Term.refine .string (.members .string ⟨{"1"}, Finset.singleton_nonempty _⟩))
    Term.boolean = some Term.never := by rfl


/-! ## The homomorphism on the read side

`Alg.AdmA_meet_both` proves the read-side homomorphism and its reading agreement once, over any
signature. DynamoDB supplies the laws of its formers (`dynFormerAdmA`) and of its leaf meet
(`dynLeafAdmA`). A literal reads through its base's codec restricted, so a literal and its base
read an attribute to one value, and two different literals at one base read nothing together. -/

/-- The conclusion of the read-side homomorphism, at one pair. -/
abbrev AdmAAt (x y z : Term) : Prop :=
  (∀ a : Attr, AdmA z a = (AdmA x a && AdmA y a)) ∧
  (∀ a : Attr, AdmA x a = true → AdmA y a = true →
    (denote z).p a = (denote x).p a ∧ (denote z).p a = (denote y).p a)

/-- Two terms whose occupancies are disjoint share no attribute, so their conjunction is
    the bottom. This closes every row that answers `never` because the two read different `Attr`
    constructors. -/
theorem AdmA_and_false {x y : Term} (h : Orth1 x y = true) (a : Attr) :
    (AdmA x a && AdmA y a) = false := by
  cases hx : AdmA x a with
  | false => simp
  | true =>
    cases hy : AdmA y a with
    | false => simp
    | true =>
      have h2 := occA_disjoint_of_Orth1 h (occA_sound x a hx)
      rw [occA_sound y a hy] at h2
      exact absurd h2 (by simp)

/-- `opaque` reads an attribute exactly where its codec answers. -/
theorem AdmA_opaq_eq (a : Attr) : AdmA .opaq a = (Ω.p a).isSome := rfl

/-- It reads every stored string, -/
theorem AdmA_opaq_str (s : String) : AdmA .opaq (.s s) = true := rfl

/-- …every stored boolean, -/
theorem AdmA_opaq_bool (b : Bool) : AdmA .opaq (.bool b) = true := rfl

/-- …every stored byte string, -/
theorem AdmA_opaq_bin (b : Bytes) : AdmA .opaq (.b b) = true := rfl

/-- …the stored null, -/
theorem AdmA_opaq_null : AdmA .opaq .null = true := rfl

/-- …and every stored numeral, as `number` reads it. -/
theorem AdmA_opaq_num (x : WFNumeral) :
    AdmA .opaq (.n x) = (numberCodec.p (.n x)).isSome := rfl

/-- Where a literal reads, its base reads the same value: `literalCodec` is `baseCodec`
    restricted, and `Codec.restrict`'s `p` returns the base's own value where the guard passes. -/
theorem literal_p_base {k : GroundKind} {x : k.Carrier} {a : Attr} {v : Value}
    (h : (literalCodec k x).p a = some v) : (baseCodec k).p a = some v := by
  rw [literalCodec_p_restrict] at h
  simp only [Alg.Codec.restrict] at h
  cases hb : (baseCodec k).p a with
  | none => rw [hb] at h; simp at h
  | some w => rw [hb] at h; simp only [Option.bind] at h; split at h <;> simp_all

/-- Where a literal reads, its base reads it to the same value. -/
theorem literal_denote_agree {k : GroundKind} {x : k.Carrier} {a : Attr}
    (h : AdmA (Term.literal k x) a = true) :
    (denote (Term.literal k x)).p a = (baseCodec k).p a := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp ((AdmA_exact _ a).mp h)
  rw [hw, literal_p_base (show (literalCodec k x).p a = some w from hw)]

/-- Where a literal reads, its base reads: the literal's codec is the base's restricted. -/
theorem AdmA_base_of_literal {k : GroundKind} {x : k.Carrier} {bt : Term} {a : Attr}
    (hb : denote bt = baseCodec k) (h : AdmA (Term.literal k x) a = true) :
    AdmA bt a = true := by
  refine (AdmA_exact bt a).mpr ?_
  rw [hb]
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp ((AdmA_exact _ a).mp h)
  rw [literal_p_base (show (literalCodec k x).p a = some w from hw)]
  rfl

/-- A literal's guard, read off a successful read: mirror of `literal_p_base`. -/
theorem literal_inL {k : GroundKind} {x : k.Carrier} {a : Attr} {v : Value}
    (h : (literalCodec k x).p a = some v) : inL k x v = true := by
  rw [literalCodec_p_restrict] at h
  simp only [Alg.Codec.restrict] at h
  cases hb : (baseCodec k).p a with
  | none => rw [hb] at h; simp at h
  | some w => rw [hb] at h; simp only [Option.bind] at h; split at h <;> simp_all

/-- **Two literals at one base and two values read nothing together.** Simp on `AdmALit` and
    `inL` does not reach the `number` row; exactness does. -/
theorem AdmALit_never_of_ne {k : GroundKind} {x y : k.Carrier} (hne : ¬ (x = y)) (a : Attr) :
    AdmA (.never : Term) a = (AdmA (Term.literal k x) a && AdmA (Term.literal k y) a) := by
  cases hx : AdmA (Term.literal k x) a with
  | false => simp [AdmA_rows]
  | true =>
      cases hy : AdmA (Term.literal k y) a with
      | false => simp [AdmA_rows]
      | true =>
          exfalso
          obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ((AdmA_exact _ a).mp hx)
          obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp ((AdmA_exact _ a).mp hy)
          have hbx := literal_p_base (show (literalCodec k x).p a = some v from hv)
          have hby := literal_p_base (show (literalCodec k y).p a = some w from hw)
          have hvw : v = w := Option.some.inj (hbx.symm.trans hby)
          subst hvw
          exact hne (inL_inj (literal_inL (show (literalCodec k x).p a = some v from hv))
            (literal_inL (show (literalCodec k y).p a = some v from hw)))

/-- **Two sets whose elements read no common attribute read no common set**, because no set is
    empty. -/
theorem AdmA_set_and_false {a y : Term} (h : ∀ u, (AdmA a u && AdmA y u) = false) (att : Attr) :
    (AdmA (.set a) att && AdmA (.set y) att) = false := by
  cases hA : AdmA (.set a) att with
  | false => rfl
  | true =>
  cases hY : AdmA (.set y) att with
  | false => rfl
  | true =>
  exfalso
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hA
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hY
  have hne : ∀ w, ((denote a).p w).isSome = true → ((denote y).p w).isSome = true → False :=
    fun w h1 h2 => by
      have := h w
      rw [(AdmA_exact a w).mpr h1, (AdmA_exact y w).mpr h2] at this
      exact Bool.noConfusion this
  rcases setCodec_p_eq.mp hp with ⟨S, rfl, hS⟩ | ⟨S, rfl, hS⟩ | ⟨S, rfl, hS⟩ <;>
    obtain ⟨x, hx⟩ := S.2
  · exact hne _ (decSet_elem hS x hx) (decSet_elem (c := denote y) (inj := Attr.s) hq x hx)
  · exact hne _ (decSet_elem hS x hx) (decSet_elem (c := denote y) (inj := Attr.n) hq x hx)
  · exact hne _ (decSet_elem hS x hx) (decSet_elem (c := denote y) (inj := Attr.b) hq x hx)

/-- **Over held-free terms, the set of the element meet reads what both sets read**, and reads
    it as both do: every held-free read is `Ω`'s. -/
theorem admA_set_meet {a y z : Term} (ha : HF a) (hy : HF y) (hz : HF z)
    (h : ∀ u, AdmA z u = (AdmA a u && AdmA y u)) : AdmAAt (.set a) (.set y) (.set z) := by
  have hr : ∀ t, ∀ w, ((denote t).p w).isSome = AdmA t w := fun t w =>
    Bool.coe_iff_coe.mp (by simpa using (AdmA_exact t w).symm)
  have h1 : ∀ att, AdmA (.set z) att = (AdmA (.set a) att && AdmA (.set y) att) := fun att => by
    apply Bool.eq_iff_iff.mpr
    rw [Bool.and_eq_true]
    show ((setCodec (denote z)).p att).isSome = true ↔
      ((setCodec (denote a)).p att).isSome = true ∧ ((setCodec (denote y)).p att).isSome = true
    rw [setCodec_p_isSome_of_sub (sub_denote z hz), setCodec_p_isSome_of_sub (sub_denote a ha),
      setCodec_p_isSome_of_sub (sub_denote y hy)]
    cases att <;> simp only [hr, h, Bool.and_eq_true, and_false, iff_self] <;>
      exact ⟨fun H => ⟨fun x hx => (H x hx).1, fun x hx => (H x hx).2⟩,
        fun H x hx => ⟨H.1 x hx, H.2 x hx⟩⟩
  refine ⟨h1, fun att hA hY => ?_⟩
  have hZ : AdmA (.set z) att = true := by rw [h1, hA, hY]; rfl
  obtain ⟨vz, hvz⟩ := Option.isSome_iff_exists.mp hZ
  obtain ⟨va, hva⟩ := Option.isSome_iff_exists.mp hA
  obtain ⟨vy, hvy⟩ := Option.isSome_iff_exists.mp hY
  have oz := (sub_setCodec (sub_denote z hz)).2 _ _ hvz
  have oa := (sub_setCodec (sub_denote a ha)).2 _ _ hva
  have oy := (sub_setCodec (sub_denote y hy)).2 _ _ hvy
  refine ⟨?_, ?_⟩
  · exact hvz.trans ((congrArg some (Option.some.inj (oz.symm.trans oa))).trans hva.symm)
  · exact hvz.trans ((congrArg some (Option.some.inj (oz.symm.trans oy))).trans hvy.symm)

/-- **Two primitives met at a primitive read as each factor reads.** -/
theorem admA_prim_some : ∀ g g' h : Ground, Ground.meet g g' = some h →
    AdmAAt (.prim g) (.prim g') (.prim h)
  | .base k, .base k', h, hp => by
      simp only [Ground.meet] at hp
      split at hp
      · next hk =>
          simp only [Option.some.injEq] at hp; subst hp hk
          exact ⟨fun a => (Bool.and_self _).symm, fun a _ _ => ⟨rfl, rfl⟩⟩
      · exact nomatch hp
  | .base k, .literal k' x, h, hp => by
      simp only [Ground.meet] at hp
      split at hp
      · next hk =>
          simp only [Option.some.injEq] at hp; subst hp hk
          refine ⟨fun a => ?_, fun a ha hb => ⟨literal_denote_agree hb, rfl⟩⟩
          cases hx : AdmA (Term.literal _ x) a with
          | false => simp
          | true => rw [AdmA_base_of_literal rfl hx]; simp
      · exact nomatch hp
  | .literal k x, .base k', h, hp => by
      simp only [Ground.meet] at hp
      split at hp
      · next hk =>
          simp only [Option.some.injEq] at hp; subst hp hk
          refine ⟨fun a => ?_, fun a ha hb => ⟨rfl, literal_denote_agree ha⟩⟩
          cases hx : AdmA (Term.literal _ x) a with
          | false => simp
          | true => rw [AdmA_base_of_literal rfl hx]; simp
      · exact nomatch hp
  | .literal k x, .literal k' x', h, hp => by
      simp only [Ground.meet] at hp
      cases k <;> cases k' <;> simp only [Ground.meetLit, reduceCtorEq] at hp <;>
        (try split at hp) <;>
        first
          | (simp only [reduceCtorEq] at hp)
          | (simp only [Option.some.injEq] at hp; subst hp; subst_vars
             exact ⟨fun a => (Bool.and_self _).symm, fun a _ _ => ⟨rfl, rfl⟩⟩)

/-- **Two primitives met at the bottom read nothing together.** -/
theorem admA_prim_none : ∀ g g' : Ground, Ground.meet g g' = none →
    ∀ a, (AdmA (.prim g) a && AdmA (.prim g') a) = false
  | .base k, .base k', hp, a => by
      simp only [Ground.meet] at hp
      split at hp
      · exact nomatch hp
      · next hk => cases k <;> cases k' <;> first | exact absurd rfl hk | exact AdmA_and_false rfl a
  | .base k, .literal k' x, hp, a => by
      simp only [Ground.meet] at hp
      split at hp
      · exact nomatch hp
      · next hk => cases k <;> cases k' <;> first | exact absurd rfl hk | exact AdmA_and_false rfl a
  | .literal k x, .base k', hp, a => by
      simp only [Ground.meet] at hp
      split at hp
      · exact nomatch hp
      · next hk => cases k <;> cases k' <;> first | exact absurd rfl hk | exact AdmA_and_false rfl a
  | .literal k x, .literal k' x', hp, a => by
      simp only [Ground.meet] at hp
      cases k <;> cases k' <;> simp only [Ground.meetLit, reduceCtorEq] at hp <;>
        (try split at hp) <;>
        first
          | (simp only [reduceCtorEq] at hp; done)
          | exact AdmA_and_false (by first | rfl | decide) a
          | (rename_i hne; rw [← AdmALit_never_of_ne hne a]; rfl)

/-- **A base reads as the top reads it.** -/
theorem admA_prim_top : ∀ g : Ground, Ground.meetTop g = true → AdmAAt (.prim g) .opaq (.prim g)
  | .base k, _ => ⟨fun a => by cases k <;> cases a <;> rfl,
      fun a ha hb => ⟨rfl, by cases k <;> cases a <;> first | rfl | cases ha⟩⟩
  | .literal _ _, h => by simp [Ground.meetTop] at h

/-- The formers of DynamoDB, on the read side. -/
instance dynFormerAdmA : Alg.FormerAdmA dynSyn where
  set_meet _ _ _ ha hy hz h := admA_set_meet ha hy hz h
  set_never _ _ h c := AdmA_set_and_false h c

/-- The leaf meet of DynamoDB is exact on the read side, and reads as each factor reads. -/
instance dynLeafAdmA : Alg.LeafAdmA dynSyn where
  prim_some g g' h hp := admA_prim_some g g' h hp
  prim_none g g' hp c := admA_prim_none g g' hp c
  prim_top g hg := admA_prim_top g hg


/-- **Where two terms have a meet, it reads exactly the attributes both read.** -/
theorem AdmA_meet {x y z : Term} (h : Term.meet x y = some z) (a : Attr) :
    AdmA z a = (AdmA x a && AdmA y a) :=
  (Alg.AdmA_meet_both x y z h).1 a

/-- **…and it reads them to the same value.** The read agreement is proved with the homomorphism
    and not after it: `AdmA (.refine t p) a` asks the predicate of what `t` decodes `a` to. -/
theorem denote_meet_p {x y z : Term} (h : Term.meet x y = some z) {a : Attr}
    (hx : AdmA x a = true) (hy : AdmA y a = true) :
    (denote z).p a = (denote x).p a ∧ (denote z).p a = (denote y).p a :=
  (Alg.AdmA_meet_both x y z h).2 a hx hy


/-! ## The bottom, and what a sub-selection keeps -/

/-- **The meet is the separation certificate, and this is its soundness half.** Where two terms
    meet at the bottom, no value is admitted by both. `Adm_meet` makes the meet's row the
    conjunction of the two rows, and the bottom admits nothing, so the conjunction is false at
    every value. `Adm_meet` and `Adm_never` each take no hypothesis, so this takes none beyond
    the meet and the test on it.

    The premise is `isNever` rather than a literal `.never` because `isNever` is what a
    certificate computes: it is the exact test over the normal form, and the literal case is
    this theorem with `rfl`. -/
theorem meet_separates {x y z : Term} (h : Term.meet x y = some z) (hz : z.isNever = true)
    (v : Value) : (Adm x v && Adm y v) = false := by
  rw [← Adm_meet x y z h v, eq_never_of_isNever hz]; exact Adm_never v

/-- …and the attribute twin, over `AdmA_meet` and `AdmA_never`, equally unpremised. -/
theorem meet_separates_A {x y z : Term} (h : Term.meet x y = some z) (hz : z.isNever = true)
    (a : Attr) : (AdmA x a && AdmA y a) = false := by
  rw [← AdmA_meet h a, eq_never_of_isNever hz]; exact AdmA_never a

/-- **A pair that meets at the bottom separates, on both halves.** `meet_separates` and
    `meet_separates_A` take the meet's answer; this reads the answer off `meetNever`. -/
theorem separates_of_meetNever {x y : Term} (h : meetNever x y = true) : Separates x y := by
  unfold meetNever at h
  cases hm : Term.meet x y with
  | none => rw [hm] at h; exact nomatch h
  | some z =>
    rw [hm] at h
    refine ⟨fun v hx hy => ?_, fun a hx hy => ?_⟩
    · have hs := meet_separates hm h v
      rw [show Adm x v = true from hx.2, show Adm y v = true from hy.2] at hs
      exact nomatch hs
    · have hs := meet_separates_A hm h a
      rw [show AdmA x a = true from hx.2, show AdmA y a = true from hy.2] at hs
      exact nomatch hs

/-! ## The views admit what the term admits -/

/-- **A set over a held-free element admits where a set over a narrower element does.** The
    held-free set writes element by element, so an element inclusion lifts to the sets. -/
theorem Adm_set_of_elem {t u : Term} (hu : HF u) (h : ∀ w, Adm t w = true → Adm u w = true)
    {v : Value} (hv : Adm (.set t) v = true) : Adm (.set u) v = true := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hv
  have el : ∀ w, ((denote t).e w).isSome = true → ((denote u).e w).isSome = true := fun w hw =>
    (Adm_exact u w).mp (h w ((Adm_exact t w).mpr hw))
  show ((setCodec (denote u)).e v).isSome = true
  rw [setCodec_e_isSome_of_sub (sub_denote u hu)]
  rcases setCodec_e_eq.mp ha with ⟨S, rfl, hS⟩ | ⟨S, rfl, hS⟩ | ⟨S, rfl, hS⟩ <;>
    exact fun x hx => el _ (encSet_elem hS x hx)

/-- …and the same on the read side. -/
theorem AdmA_set_of_elem {t u : Term} (hu : HF u) (h : ∀ w, AdmA t w = true → AdmA u w = true)
    {att : Attr} (ha : AdmA (.set t) att = true) : AdmA (.set u) att = true := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ha
  have el : ∀ w, ((denote t).p w).isSome = true → ((denote u).p w).isSome = true := fun w hw =>
    (AdmA_exact u w).mp (h w ((AdmA_exact t w).mpr hw))
  show ((setCodec (denote u)).p att).isSome = true
  rw [setCodec_p_isSome_of_sub (sub_denote u hu)]
  rcases setCodec_p_eq.mp hv with ⟨S, rfl, hS⟩ | ⟨S, rfl, hS⟩ | ⟨S, rfl, hS⟩ <;>
    exact fun x hx => el _ (decSet_elem hS x hx)

/-- A term whose caller-side view admits each value that the term admits. -/
def WriteLe (t : Term) : Prop := RowLe (Adm t) (Adm (writeView t))
/-- Each term of the list has `WriteLe`. -/
def WriteLeL : List Term → Prop
  | [] => True
  | t :: ts => WriteLe t ∧ WriteLeL ts
/-- The term, where one is present, has `WriteLe`. -/
def WriteLeO : Option Term → Prop
  | none => True
  | some t => WriteLe t
/-- A term whose stored-side view reads each attribute that the term reads. -/
def ReadLe (t : Term) : Prop := RowLe (AdmA t) (AdmA (readView t))
/-- Each term of the list has `ReadLe`. -/
def ReadLeL : List Term → Prop
  | [] => True
  | t :: ts => ReadLe t ∧ ReadLeL ts
/-- The term, where one is present, has `ReadLe`. -/
def ReadLeO : Option Term → Prop
  | none => True
  | some t => ReadLe t

/-- The rows of a list of terms, beside the rows of their caller-side views. -/
theorem writeLeL_forall₂ :
    ∀ ts, WriteLeL ts → List.Forall₂ RowLe (AdmList ts) (AdmList (writeViewL ts))
  | [], _ => .nil
  | _ :: ts, h => .cons h.1 (writeLeL_forall₂ ts h.2)

/-- The row of a spread, beside the row of its caller-side view. -/
theorem writeLeO_rel : ∀ o, WriteLeO o → Option.Rel RowLe (AdmOptT o) (AdmOptT (writeViewO o))
  | none, _ => .none
  | some _, h => .some h

/-- The stored rows of a list of terms, beside the rows of their stored-side views. -/
theorem readLeL_forall₂ :
    ∀ ts, ReadLeL ts → List.Forall₂ RowLe (AdmAList ts) (AdmAList (readViewL ts))
  | [], _ => .nil
  | _ :: ts, h => .cons h.1 (readLeL_forall₂ ts h.2)

/-- The stored row of a spread, beside the row of its stored-side view. -/
theorem readLeO_rel : ∀ o, ReadLeO o → Option.Rel RowLe (AdmAOptT o) (AdmAOptT (readViewO o))
  | none, _ => .none
  | some _, h => .some h

/-- A list whose positions have `WriteLe` has `WriteLe`. -/
theorem writeLe_list {pre suf : List Term} {sp : Option Term} (hp : WriteLeL pre)
    (hs : WriteLeO sp) (hf : WriteLeL suf) : WriteLe (.list pre sp suf) := by
  intro v h
  cases v with
  | arr vs =>
    exact alignPL_mono (writeLeL_forall₂ pre hp) (writeLeO_rel sp hs)
      (writeLeL_forall₂ suf hf) vs h
  | _ => exact absurd h (by simp [Adm_rows])

/-- A list whose positions have `ReadLe` has `ReadLe`. -/
theorem readLe_list {pre suf : List Term} {sp : Option Term} (hp : ReadLeL pre)
    (hs : ReadLeO sp) (hf : ReadLeL suf) : ReadLe (.list pre sp suf) := by
  intro a h
  cases a with
  | l as =>
    exact alignPL_mono (readLeL_forall₂ pre hp) (readLeO_rel sp hs)
      (readLeL_forall₂ suf hf) as h
  | _ => exact absurd h (by simp [AdmA_rows])

/-- An object whose slots and open block have `WriteLe` has `WriteLe`. The view keeps each
    presence mark, so the presence test does not move. -/
theorem writeLe_object {fs : Finset Name} {f : {k // k ∈ fs} → ObjectSlot} {w : Option Term}
    (hf : ∀ k, RowLe (AdmField (f k)) (AdmField (writeViewS (f k)))) (hw : WriteLeO w) :
    WriteLe (.object (.mk fs f w)) := by
  intro v h
  cases v with
  | map keys g =>
    simp only [writeView, writeViewB, Adm_rows, Bool.and_eq_true] at h ⊢
    refine ⟨decide_eq_true fun k => ?_, decide_eq_true fun k => ?_⟩
    · have := of_decide_eq_true h.1 k
      beta_reduce
      generalize f k = s at this ⊢
      cases s <;> simp_all [writeViewS]
    · have := of_decide_eq_true h.2 k
      rcases Decidable.em (k.1 ∈ fs) with hm | hm
      · simp only [entryP, MapOf.at, dif_pos hm] at this ⊢
        exact hf ⟨k.1, hm⟩ _ this
      · simp only [entryP, MapOf.at, dif_neg hm] at this ⊢
        cases w with
        | none => exact absurd this (by simp [Adm_rows])
        | some t => exact hw _ this
  | _ => exact absurd h (by simp [Adm_rows])

/-- An object whose slots and open block have `ReadLe` has `ReadLe`. -/
theorem readLe_object {fs : Finset Name} {f : {k // k ∈ fs} → ObjectSlot} {w : Option Term}
    (hf : ∀ k, RowLe (AdmAField (f k)) (AdmAField (readViewS (f k)))) (hw : ReadLeO w) :
    ReadLe (.object (.mk fs f w)) := by
  intro a h
  cases a with
  | m keys g =>
    simp only [readView, readViewB, AdmA_rows, Bool.and_eq_true] at h ⊢
    refine ⟨decide_eq_true fun k => ?_, decide_eq_true fun k => ?_⟩
    · have := of_decide_eq_true h.1 k
      beta_reduce
      generalize f k = s at this ⊢
      cases s <;> simp_all [readViewS]
    · have := of_decide_eq_true h.2 k
      rcases Decidable.em (k.1 ∈ fs) with hm | hm
      · simp only [entryP, MapOf.at, dif_pos hm] at this ⊢
        exact hf ⟨k.1, hm⟩ _ this
      · simp only [entryP, MapOf.at, dif_neg hm] at this ⊢
        cases w with
        | none => exact absurd this (by simp [AdmA_rows])
        | some t => exact hw _ this
  | _ => exact absurd h (by simp [AdmA_rows])

/-- The views of a list admit where the list admits. -/
theorem anyWrite : ∀ ts : List Term, WriteLeL ts → ∀ v, AdmAny ts v = true →
    AdmAny (writeViewL ts) v = true
  | [], _, _, h => h
  | _ :: ts, hw, v, h => by
      simp only [AdmAny_cons, writeViewL, Bool.or_eq_true] at h ⊢
      exact h.imp (hw.1 v) (anyWrite ts hw.2 v)

/-- The stored views of a list read where the list reads. -/
theorem anyRead : ∀ ts : List Term, ReadLeL ts → ∀ a, AdmAAny ts a = true →
    AdmAAny (readViewL ts) a = true
  | [], _, _, h => h
  | _ :: ts, hr, a, h => by
      simp only [AdmAAny_cons, readViewL, Bool.or_eq_true] at h ⊢
      exact h.imp (hr.1 a) (anyRead ts hr.2 a)

mutual
/-- **The caller-side view admits each value that the term admits.** -/
theorem writeLe_of : ∀ t : Term, WriteLe t
  | .held _ P _ _ => fun v h => by
      simp only [writeView]
      exact writeLe_of P v (Bool.and_eq_true_iff.mp h).2
  | .var _ => fun _ h => h
  | .mu _ => fun _ h => h
  | .refine t p => fun v h => by
      simp only [writeView, Adm_rows, Bool.and_eq_true] at h ⊢
      exact ⟨writeLe_of t v h.1, h.2⟩
  | .list pre sp suf => writeLe_list (writeLe_ofL pre) (writeLe_ofO sp) (writeLe_ofL suf)
  | .object (.mk fs f w) => writeLe_object (fun k => writeLe_ofS (f k)) (writeLe_ofO w)
  | .union os => fun v h => by
      simp only [writeView]
      rw [Adm_union] at h ⊢
      exact anyWrite os (writeLe_ofL os) v h
  | .base _ => fun _ h => h | .literal _ _ => fun _ h => h
  | .set t => fun v h => by
      simp only [writeView]
      split
      · exact h
      · next hh =>
        exact Adm_set_of_elem (HF_of_hasHeld _ (Bool.eq_false_iff.mpr hh))
          (fun w hw => writeLe_of t w hw) h
  | .opaq => fun _ h => h | .never => fun _ h => h
/-- `writeLe_of` over a list. -/
theorem writeLe_ofL : ∀ ts : List Term, WriteLeL ts
  | [] => trivial
  | t :: ts => ⟨writeLe_of t, writeLe_ofL ts⟩
/-- `writeLe_of` at an optional term. -/
theorem writeLe_ofO : ∀ o : Option Term, WriteLeO o
  | none => trivial
  | some t => writeLe_of t
/-- `writeLe_of` at a slot. -/
theorem writeLe_ofS : ∀ s : ObjectSlot, RowLe (AdmField s) (AdmField (writeViewS s))
  | .req t => fun v h => writeLe_of t v h
  | .optional t => fun v h => writeLe_of t v h
end

mutual
/-- **The stored-side view reads each attribute that the term reads.** -/
theorem readLe_of : ∀ t : Term, ReadLe t
  | .held t _ _ _ => fun a h => by
      simp only [readView]
      exact readLe_of t a (Bool.and_eq_true_iff.mp h).1
  | .var _ => fun _ h => h
  | .mu _ => fun _ h => h
  | .refine t p => fun a h => by
      simp only [readView]
      split
      · exact readLe_of t a (Bool.and_eq_true_iff.mp h).1
      · exact h
  | .list pre sp suf => readLe_list (readLe_ofL pre) (readLe_ofO sp) (readLe_ofL suf)
  | .object (.mk fs f w) => readLe_object (fun k => readLe_ofS (f k)) (readLe_ofO w)
  | .union os => fun a h => by
      simp only [readView]
      rw [AdmA_union] at h ⊢
      exact anyRead os (readLe_ofL os) a h
  | .base _ => fun _ h => h | .literal _ _ => fun _ h => h
  | .set t => fun a h => by
      simp only [readView]
      split
      · exact h
      · next hh =>
        exact AdmA_set_of_elem (HF_of_hasHeld _ (Bool.eq_false_iff.mpr hh))
          (fun w hw => readLe_of t w hw) h
  | .opaq => fun _ h => h | .never => fun _ h => h
/-- `readLe_of` over a list. -/
theorem readLe_ofL : ∀ ts : List Term, ReadLeL ts
  | [] => trivial
  | t :: ts => ⟨readLe_of t, readLe_ofL ts⟩
/-- `readLe_of` at an optional term. -/
theorem readLe_ofO : ∀ o : Option Term, ReadLeO o
  | none => trivial
  | some t => readLe_of t
/-- `readLe_of` at a slot. -/
theorem readLe_ofS : ∀ s : ObjectSlot, RowLe (AdmAField s) (AdmAField (readViewS s))
  | .req t => fun a h => readLe_of t a h
  | .optional t => fun a h => readLe_of t a h
end

/-- **The certificate through the views is sound.** A value that both terms admit is admitted
    by both caller-side views, and an attribute that both terms read is read by both stored-side
    views. The views are held-free, so the meet separates each pair of views. -/
theorem separates_of_certViews {x y : Term} (h : certViews x y = true) : Separates x y := by
  simp only [certViews, Bool.and_eq_true] at h
  obtain ⟨⟨_, hw⟩, hr⟩ := h
  have sw := separates_of_meetNever hw
  have sr := separates_of_meetNever hr
  refine ⟨fun v hx hy => ?_, fun a hx hy => ?_⟩
  · have hx' := writeLe_of x v hx.2
    have hy' := writeLe_of y v hy.2
    exact sw.1 v ⟨occV_sound (writeView x) v hx', hx'⟩ ⟨occV_sound (writeView y) v hy', hy'⟩
  · have hx' := readLe_of x a hx.2
    have hy' := readLe_of y a hy.2
    exact sr.2 a ⟨occA_sound (readView x) a hx', hx'⟩ ⟨occA_sound (readView y) a hy', hy'⟩

/-- **The slot test is sound.** Each family of `Separates` holds the occupancy as a conjunct, and
    `Orth1` makes the two occupancies disjoint on each side. -/
theorem separates_of_Orth1 {x y : Term} (h : Orth1 x y = true) : Separates x y :=
  ⟨fun _ hx hy => occV_disjoint_of_Orth1 h hx.1 hy.1,
   fun _ hx hy => occA_disjoint_of_Orth1 h hx.1 hy.1⟩

/-- **The pair certificate is sound**: each disjunct separates the pair. -/
theorem separates_of_certPair {x y : Term} (h : certPair x y = true) : Separates x y := by
  simp only [certPair, Bool.or_eq_true] at h
  rcases h with (hm | hv) | ho
  · exact separates_of_meetNever hm
  · exact separates_of_certViews hv
  · exact separates_of_Orth1 ho

/-- **A certified union is separated**, which is the premise of `pairwiseCompat_of_separated`
    and of `admitsAtMostOne_of_separated`. -/
theorem separated_of_unionOk {os : List Term} (h : unionOk os = true) : Separated os :=
  (pairwise_of_certAll h).imp separates_of_certPair

/-- `certAll` from the pairwise form, which is what a sublist preserves. -/
theorem certAll_of_pairwise : ∀ {ts : List Term},
    List.Pairwise (fun x y => certPair x y = true) ts → certAll ts = true
  | [], _ => rfl
  | t :: ts, h => by
      cases h with
      | cons hh hrest =>
        simp only [certAll, Bool.and_eq_true, List.all_eq_true]
        exact ⟨fun u hu => hh u hu, certAll_of_pairwise hrest⟩


/-! ## The laws, on admission

`Adm_meet` is the homomorphism from the meet to conjunction, so each law below is the
corresponding law of `Bool` read through it. Each is stated on both sides ANSWERING: whether the
meet answers in one order when it answers in the other is a question about the rows, and the
lattice does not need it.
-/

/-- **The meet is commutative on admission.** Stated on both orders answering, because whether
    the meet answers in one order when it answers in the other is a question about the rows and
    not about the lattice. -/
theorem Adm_meet_comm {x y z z' : Term} (h : Term.meet x y = some z)
    (h' : Term.meet y x = some z') (v : Value) : Adm z v = Adm z' v := by
  rw [Adm_meet _ _ _ h, Adm_meet _ _ _ h', Bool.and_comm]

/-- **…and associative on admission**, both bracketings answering. -/
theorem Adm_meet_assoc {x y z xy yz l r : Term}
    (hxy : Term.meet x y = some xy) (hl : Term.meet xy z = some l)
    (hyz : Term.meet y z = some yz) (hr : Term.meet x yz = some r) (v : Value) :
    Adm l v = Adm r v := by
  rw [Adm_meet _ _ _ hl, Adm_meet _ _ _ hxy, Adm_meet _ _ _ hr, Adm_meet _ _ _ hyz, Bool.and_assoc]

/-- **…and idempotent.** -/
theorem Adm_meet_self {x z : Term} (h : Term.meet x x = some z) (v : Value) :
    Adm z v = Adm x v := by
  rw [Adm_meet _ _ _ h, Bool.and_self]

/-- **The bottom absorbs.** -/
theorem Adm_meet_never {x z : Term} (h : Term.meet x .never = some z) (v : Value) :
    Adm z v = false := by
  rw [Adm_meet _ _ _ h, Adm_never, Bool.and_false]

/-- **The meet distributes over a union.** `AdmAny` is the join of the options' admissions,
    and `&&` distributes over `||`. -/
theorem Adm_meet_union {x z : Term} {os : List Term}
    (h : Term.meet x (.union os) = some z) (v : Value) :
    Adm z v = (Adm x v && AdmAny os v) := by
  rw [Adm_meet _ _ _ h, Adm_union]

/-- …and the distribution, written so a reader sees it: the meet of a term with a join is the
    join of the meets, one option at a time. -/
theorem Adm_meet_union_distrib {x z o : Term} {os : List Term}
    (h : Term.meet x (.union (o :: os)) = some z) (v : Value) :
    Adm z v = ((Adm x v && Adm o v) || (Adm x v && AdmAny os v)) := by
  rw [Adm_meet_union h, AdmAny_cons]
  cases Adm x v <;> cases Adm o v <;> cases AdmAny os v <;> rfl

/-! ## The laws, on reading

`AdmA_meet` is the homomorphism from the meet to conjunction on the read side, so each law
below is the corresponding law of `Bool` read through it, exactly as the admission laws are.
Each is stated on both sides ANSWERING, for the same reason: whether the meet answers in one
order when it answers in the other is a question about the rows, and the lattice does not need
it.
-/

/-- **The meet is commutative on reading.** -/
theorem AdmA_meet_comm {x y z z' : Term} (h : Term.meet x y = some z)
    (h' : Term.meet y x = some z') (a : Attr) : AdmA z a = AdmA z' a := by
  rw [AdmA_meet h, AdmA_meet h', Bool.and_comm]

/-- **…and associative on reading**, both bracketings answering. -/
theorem AdmA_meet_assoc {x y z xy yz l r : Term}
    (hxy : Term.meet x y = some xy) (hl : Term.meet xy z = some l)
    (hyz : Term.meet y z = some yz) (hr : Term.meet x yz = some r) (a : Attr) :
    AdmA l a = AdmA r a := by
  rw [AdmA_meet hl, AdmA_meet hxy, AdmA_meet hr, AdmA_meet hyz, Bool.and_assoc]

/-- **…and idempotent.** -/
theorem AdmA_meet_self {x z : Term} (h : Term.meet x x = some z) (a : Attr) :
    AdmA z a = AdmA x a := by
  rw [AdmA_meet h, Bool.and_self]

/-- **The bottom absorbs**, and it reads nothing. -/
theorem AdmA_meet_never {x z : Term} (h : Term.meet x .never = some z) (a : Attr) :
    AdmA z a = false := by
  rw [AdmA_meet h, AdmA_never, Bool.and_false]

/-- **The meet distributes over a union.** `AdmAAny` is the join of the options' readings,
    and `&&` distributes over `||`. -/
theorem AdmA_meet_union {x z : Term} {os : List Term}
    (h : Term.meet x (.union os) = some z) (a : Attr) :
    AdmA z a = (AdmA x a && AdmAAny os a) := by
  rw [AdmA_meet h, AdmA_union os a]

/-- …and the distribution, written so a reader sees it: the meet of a term with a join is the
    join of the meets, one option at a time. -/
theorem AdmA_meet_union_distrib {x z o : Term} {os : List Term}
    (h : Term.meet x (.union (o :: os)) = some z) (a : Attr) :
    AdmA z a = ((AdmA x a && AdmA o a) || (AdmA x a && AdmAAny os a)) := by
  rw [AdmA_meet_union h, AdmAAny_cons]
  cases AdmA x a <;> cases AdmA o a <;> cases AdmAAny os a <;> rfl


end Calculus
