import Calculus.Lang.DisjointA
import Calculus.Dynamo.Lang.HeldSet
import Calculus.Dynamo.Lang.HeldFree
import Calculus.Dynamo.Analysis.Merge
import Calculus.Dynamo.Analysis.Orthogonality
import Calculus.Dynamo.Analysis.Laminar

variable {α : Calculus.Table}

/-!
# Disjointness at DynamoDB, and the union certificate

`Alg.Term.disjoint` decides that two terms share no value, and `Alg.disjoint_orthogonal` proves
the decision sound over any signature. DynamoDB supplies the leaves (`dynLeaf`): two primitives
meet at a primitive or at the bottom, and two data predicates meet at a predicate or at the empty
predicate. DynamoDB supplies the laws of the leaves and of the set former (`dynLeafAdm`,
`dynFormerAdm` and their read-side twins), and the shape classes (`dynShapes`).

**The certificate reads the views, not the terms.** A term denotes a partial isomorphism.
The caller view states its domain, and the stored view states its range. A `held` carries an adapter word,
and the test reads no table, so the test reads a raw `held` as disjoint from the bottom alone. The views replace each `held`
by a term that bounds its domain or its range, so the certificate asks the test of the two pairs
of views (`certPair`). Two terms whose domains are disjoint and whose ranges are disjoint are
orthogonal: no value has two writers, and no attribute has two readers.

**The two halves part at a `held`.** A `held` writes where its caller-side term writes and reads
where its inner term reads, so an adapter and a native of the adapter's stored kind are disjoint
on the write half and not on the read half. The certificate asks both halves.
-/

namespace Calculus

open Alg (Orient Term.isNever ObjectSlot.isReq Body.fields_mk Body.wild_mk Body.at_mk Body.block)

export Alg (Term.ofOptions hasHeld pair0)


/-! ## Reading a field and a term -/

/-- Whether a predicate is data that the test can compare with another. `closure` is the
    caller's own function and is the one case `Pred` keeps open. -/
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

/-- Where the meet is empty, nothing satisfies both. -/
theorem meetM_empty {q p : Pred} (h : Pred.meetM q p = some none) (v : Value) :
    (Pred.eval q v && Pred.eval p v) = false := by
  have hok := meetM_ok q p
  rw [h] at hok
  exact hok v


/-! ## The leaves of DynamoDB

The test is `Alg.Term.disjoint`, the structural test over a universe signature. DynamoDB supplies
the leaves `dynLeaf`: two primitives, and two predicates. -/

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

/-- **The leaves of DynamoDB.** -/
instance dynLeaf : Alg.Leaf dynSig where
  prim := Ground.meet
  isData s := Alg.half (X := fun s => dynP s → Bool) s Pred.isData fun _ => false
  pmeet s := Alg.half (X := fun s => dynP s → dynP s → Option (Option (dynP s))) s Pred.meetM
    fun _ _ => none

/-- A closed traversal and a traversal through a block that admits nothing agree. -/
theorem objAdmV_none_never {α : Type} (fs : MapOf (α → Bool)) (keys : Finset Name)
    (g : {k // k ∈ keys} → α) :
    objAdmV fs none keys g = objAdmV fs (some (fun _ => false)) keys g := by
  unfold objAdmV
  exact decide_eq_decide.mpr (forall_congr' fun k => by unfold entryP; cases fs.at k.1 <;> exact Iff.rfl)


/-- **The closed body is the open body whose block is `never`**, on the write side. -/
theorem Adm_closed_eq_never_block (D : Finset Name) (f : {k // k ∈ D} → ObjectSlot) :
    Adm α (.object (.mk D f none)) = Adm α (.object (.mk D f (some .never))) := by
  funext v
  cases v with
  | m keys g =>
      show (valPresentT D f keys && objAdmV _ none keys g) =
        (valPresentT D f keys && objAdmV _ (some (fun _ => false)) keys g)
      rw [objAdmV_none_never]
  | _ => rfl

/-- …and on the read side. -/
theorem AdmA_closed_eq_never_block (D : Finset Name) (f : {k // k ∈ D} → ObjectSlot) :
    AdmA α (.object (.mk D f none)) = AdmA α (.object (.mk D f (some .never))) := by
  funext a
  cases a with
  | m keys g =>
      change (valPresentT D _ keys && objAdmV _ none keys g) =
        (valPresentT D _ keys && objAdmV _ (some (fun _ => false)) keys g)
      rw [objAdmV_none_never]
  | _ => rfl

/-! ## The union certificate

The certificate is defined here, after the leaves, because the test of the views reads them. -/

mutual
/-- **The view at an orientation**: each `held` becomes its term at the caller side of the
    orientation: its outer where its side is that caller side, and its inner term otherwise. The
    view admits at the orientation each value that the term admits (`viewLe_of`). The view of a
    `union` is the union of the views, because a union admits where one of its options admits.
    The view at the host is the caller view, and the view at the dual is the stored view.

    The view of `mu b` is `mu` of the view of `b`, and a variable stays a variable. Each stage of
    the view admits what the same stage of the term admits, so the view of a recursive term
    admits what the term admits. The view holds no `held` (`HF_view`), so a set of the view acts
    element by element.

    **Over a held-free closed inner term, the view keeps a refinement as it is.** Elsewhere the
    inner term can hold a `held`: a variable denotes a stage of its binder, and the stage can hold
    a `held`, so a variable counts as a possible `held`. The orientation tests the predicate of
    its caller side directly, and tests the predicate of its stored side through the map of the
    inner term, which runs the adapter. The view keeps no adapter, so the view keeps the first
    predicate and drops the second. DynamoDB states no stored predicate (`()` is the truth). So
    at the host the second predicate is the truth, and the view keeps the refinement over the
    view of the inner term. At the dual the second predicate is the data predicate, and the view
    is the view of the inner term.

    **The stored view is narrower than it can be, and no certificate observes the
    difference.** A variable holds a `held` only where its binder's body holds one, so a finer
    view keeps more predicates over a variable. `Term.disjoint` compares a data predicate only
    over a closed held-free inner term, so a predicate over a variable changes no verdict. An
    example after `separates_of_certPair` pins the narrowing. -/
def view (o : Orient) : Term → Term
  | .held s t P _ _ => bif s == o.c then view o P else view o t
  | .refine t p pA =>
      if hasHeld t || t.hasVar then bif o.c then view o t else .refine (view o t) p pA
      else .refine t p pA
  | .list pre sp suf => .list (viewL o pre) (viewO o sp) (viewL o suf)
  | .object b => .object (viewB o b)
  | .union os => .union (viewL o os)
  | .set t => .set (view o t)
  | .mu b => .mu (view o b)
  | t => t
def viewL (o : Orient) : List Term → List Term
  | [] => []
  | t :: ts => view o t :: viewL o ts
def viewO (o : Orient) : Option Term → Option Term
  | none => none
  | some t => some (view o t)
def viewB (o : Orient) : Body → Body
  | .mk fs f w => .mk fs (fun k => viewS o (f k)) (viewO o w)
def viewS (o : Orient) : ObjectSlot → ObjectSlot
  | .req t => .req (view o t)
  | .optional t => .optional (view o t)
end

/-- **Whether the two pairs of views are disjoint.** A term denotes a partial isomorphism.
    The caller view states its domain and the stored view states its range. Two terms
    whose domains are disjoint and whose ranges are disjoint are orthogonal. -/
def viewsDisjoint (x y : Term) : Bool :=
  Alg.Term.disjoint pair0 (view .host x) (view .host y) &&
    Alg.Term.disjoint pair0 (view .dual x) (view .dual y)

/-- **The certificate for one pair of options**: orthogonality. The domains are disjoint and the
    ranges are disjoint, so the product of the two domain idempotents is zero and the product of
    the two range idempotents is zero: the two options are orthogonal elements of an inverse
    semigroup (Lawson, *Primer on inverse semigroups I*, Lemma 2.16). So no value has two writers
    and no attribute has two readers (`viewsDisjoint_adm`, `viewsDisjoint_admA`).

    **The views state the domain and the range of a `held`**, which the test does not read on a
    raw term. On a term with no `held`, the caller view is the term, and the stored view keeps
    each predicate over a closed held-free inner term.

    **A `refine` at a `closure` has an admission that is a function.** The test reads it through
    its inner term. So `refine string (closure q)` beside `list [] (some number) []` is
    certified, because `string` beside the list is disjoint. -/
def certPair (x y : Term) : Bool := viewsDisjoint x y

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

/-! ## What the rows answer

Worked pairs, one per class, checked by the kernel rather than described. -/

/-- Two value kinds share no value. -/
example : Alg.Term.disjoint pair0 Term.string Term.number = true := by rfl

/-- A literal shares its value with its own base… -/
example : Alg.Term.disjoint pair0 (Term.literal .string "a") Term.string = false := by rfl

/-- …and shares nothing with another value of the same base. -/
example : Alg.Term.disjoint pair0 (Term.literal .string "a") (Term.literal .string "b") = true := by
  rfl

/-- A literal at a base that shares nothing with the partner is disjoint from it. -/
example : Alg.Term.disjoint pair0 (Term.literal .string "1") Term.boolean = true := by rfl

/-- **The null point needs no row of its own.** A null point is the null term joined by a union,
    so the union row reads each option. The top holds the null point, and a `null` shares it. -/
example : Alg.Term.disjoint pair0 (Term.union [.string, .null]) Term.opaq = false := by rfl

example : Alg.Term.disjoint pair0 (Term.union [.string, .null]) Term.null = false := by rfl

/-- **Two open objects are not disjoint where each holds the other's names.** The left body
    requires `x`, and the right body holds `x` in its open block. The two examples below are a
    value both admit. -/
example : Alg.Term.disjoint pair0
    (Term.object (.mk {"x"} (fun _ => .req .string) (some .string)))
    (Term.object (.mk {"y"} (fun _ => .optional .string) (some .string))) = false := by rfl

/-- The left body admits `{x := "1"}` through its declared slot… -/
example : Adm α (.object (.mk {"x"} (fun _ => .req .string) (some .string)))
    (.map {"x"} (fun _ => .str "1")) = true := by
  simp [Adm_rows, valPresentT, objAdmV, entryP, MapOf.at, inBase]

/-- …and the right body admits it through its open block, at a name it does not declare. -/
example : Adm α (.object (.mk {"y"} (fun _ => .optional .string) (some .string)))
    (.map {"x"} (fun _ => .str "1")) = true := by
  simp [Adm_rows, valPresentT, objAdmV, entryP, MapOf.at]
  apply decide_eq_true
  intro k
  rw [if_neg (by have hk := k.2; simp only [Finset.mem_singleton] at hk; simp [hk])]
  rfl

/-! ### The presence table

A slot pair is disjoint only where one slot requires the name: two optional slots both admit a
map without the name. -/

/-- A required slot beside an optional slot of a disjoint term is disjoint. -/
example : Alg.ObjectSlot.disjoint pair0 (ObjectSlot.req .string) (ObjectSlot.optional .boolean)
    = true := by rfl

/-- Two optional slots are never disjoint. -/
example : Alg.ObjectSlot.disjoint pair0 (ObjectSlot.optional .string)
    (ObjectSlot.optional .boolean) = false := by rfl

/-- **Two closed objects with no shared name and no required name are not disjoint**: both
    admit the empty map. -/
example : Alg.Term.disjoint pair0
    (Term.object (.mk {"x"} (fun _ => .optional .string) none))
    (Term.object (.mk {"y"} (fun _ => .optional .string) none)) = false := by rfl

/-- **Two objects that declare one name with one mark and no literal are certified**: the
    required slots hold `string` and `boolean`, which are disjoint. -/
example : unionOk [.object (.mk {"a"} (fun _ => .req .string) none),
    .object (.mk {"a"} (fun _ => .req .boolean) none)] = true := by decide

/-! ### A required position and an element

A position that must hold a value keeps two shapes apart where the two position terms are
disjoint. An element of an `array` does not, because every array holds the empty list. -/

/-- A tuple's declared position is such a position… -/
example : Alg.Term.disjoint pair0 (Term.tuple [.string] none) (Term.tuple [.boolean] none)
    = true := by rfl

/-- …an `array`'s element is not. -/
example : Alg.Term.disjoint pair0 (Term.array .string) (Term.array .boolean) = false := by rfl

/-- A refinement is disjoint from what its inner term is disjoint from. -/
example : Alg.Term.disjoint pair0
    (Term.refine .string (.members .string ⟨{"1"}, Finset.singleton_nonempty _⟩) ()) Term.null
      = true := by rfl

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
its own. Each pair is disjoint. -/

/-- The three options: a nonempty list of `"A"`, a nonempty list of `"B"`, and the empty list. -/
def literalListOptions : List Term :=
  [.list [.literal .string "A"] (some (.literal .string "A")) [],
   .list [.literal .string "B"] (some (.literal .string "B")) [],
   .list [] none []]

/-- **The test certifies the union**: each pair is disjoint. -/
theorem unionOk_literalListOptions : unionOk literalListOptions = true := by decide

/-- **The crossing control is not certified.** `array (literal "A")` and `array (literal "B")`
    both hold `[]`. -/
theorem not_unionOk_literalArrays :
    unionOk [.array (.literal .string "A"), .array (.literal .string "B")] = false := by decide

/-! ### Two restricted sets, apart at their elements

The test certifies two string sets whose members are disjoint, because the elements are
disjoint and no set is empty. -/

/-- **Two string sets with disjoint members are disjoint.** -/
theorem disjoint_disjointStringSets :
    Alg.Term.disjoint pair0 (.set (.refine .string (.members .string (NEFinset.of "a" {"b"})) ()) : Term)
      (.set (.refine .string (.members .string (NEFinset.of "c" ∅)) ()) : Term) = true := by
  decide

/-- **Two string sets that share a member are not disjoint.** -/
theorem not_disjoint_stringSets_shared :
    Alg.Term.disjoint pair0 (.set (.refine .string (.members .string (NEFinset.of "a" {"b"})) ()) : Term)
      (.set (.refine .string (.members .string (NEFinset.of "b" {"c"})) ()) : Term) = false := by
  decide

/-! ### The views certify a `held` whose caller side is precise

A string set held as a list of strings, beside a list of numbers. Both terms write a list, and
the test does not read a raw `held`, so the test of the two terms does not certify the pair. The
caller-side views are disjoint when the caller side requires one element or more, and the
stored-side views differ in kind. -/

/-- The test of the two terms does not certify the pair. -/
theorem disjoint_heldNE_base :
    Alg.Term.disjoint pair0 (.held false (.set .string) (.list [.string] (some .string) []) (.caller 0, false) [] : Term)
        (.list [] (some .number) [] : Term) = false := by
  decide

/-- **A caller side that requires one element or more is certified** beside a list of numbers. -/
theorem certPair_heldNE :
    certPair (.held false (.set .string) (.list [.string] (some .string) []) (.caller 0, false) [])
      (.list [] (some .number) []) = true := by
  decide

/-- **A caller side that admits the empty list is refused**, because the list of numbers admits
    the empty list too. -/
theorem certPair_heldAny :
    certPair (.held false (.set .string) (.list [] (some .string) []) (.caller 0, false) [])
      (.list [] (some .number) []) = false := by
  decide

/-- **A `held` below a recursion is certified where the views part.** The caller view of the
    recursive term is `mu (union [literal "1", list [] (some (var 0)) []])`, and the stored view
    is `mu (union [number, list [] (some (var 0)) []])`. Each is disjoint from
    `literal "A" ∪ literal "B"`. -/
theorem certPair_heldBelowMu :
    certPair (.union [.literal .string "A", .literal .string "B"])
      (.mu (.union [.held false .number (.literal .string "1") (.caller 0, false) [], .list [] (some (.var 0)) []]))
      = true := by
  decide

/-- …and the pair is refused where the caller views share a value: the text `"1"`. -/
theorem certPair_heldBelowMu_meets :
    certPair (.literal .string "1")
      (.mu (.union [.held false .number (.literal .string "1") (.caller 0, false) [], .list [] (some (.var 0)) []]))
      = false := by
  decide

/-- **The test does not read a raw `held`.** A `held` carries an adapter word, and the test reads
    no table, so the test keeps the `held` apart from the bottom alone. The views read it. -/
example : Alg.Term.disjoint pair0 (Term.held false .string .opaq (.caller 0, false) [])
    Term.number = false := by rfl

/-! ## The levers -/

/-! ## DynamoDB is an instance of the laws, on the write side

`Alg.disjoint_sound` proves the write side once, over any signature. DynamoDB supplies the law of
its set former (`dynFormerAdm`) and the laws of its leaves (`dynLeafAdm`). A primitive law is a
fact about `inBase` and `inL`, and the set law is a fact about `setCodec`. The disjointness of
two formers is a theorem of the shape classes (`dynShapes`). -/

/-- **`ofOptions` admits what its options admit**, and no certificate is spent. -/
theorem Adm_ofOptions (ts : List Term) (v : Value) :
    Adm α (Term.ofOptions ts) v = AdmAny α ts v := by
  match ts with
  | [] => rfl
  | [t] => simp only [Term.ofOptions, AdmAny_cons, AdmAny_nil, Bool.or_false]
  | _ :: _ :: _ => rfl

/-- **Two sets whose elements share no value share no set**, because no set is empty. -/
theorem Adm_set_and_false {a y : Term} (h : ∀ u, (Adm α a u && Adm α y u) = false) (v : Value) :
    (Adm α (.set a) v && Adm α (.set y) v) = false := by
  cases hA : Adm α (.set a) v with
  | false => rfl
  | true =>
  cases hY : Adm α (.set y) v with
  | false => rfl
  | true =>
  exfalso
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hA
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hY
  have hne : ∀ w, ((denote α a).e w).isSome = true → ((denote α y).e w).isSome = true → False :=
    fun w h1 h2 => by
      have := h w
      rw [(Adm_exact a w).mpr h1, (Adm_exact y w).mpr h2] at this
      exact Bool.noConfusion this
  rcases setCodec_f_eq.mp hp with ⟨S, rfl, hS⟩ | ⟨S, rfl, hS⟩ | ⟨S, rfl, hS⟩ <;>
    obtain ⟨x, hx⟩ := S.2
  · exact hne _ (setAt_elem hS x hx) (setAt_elem (c := denote α y) (inj := Value.str) hq x hx)
  · exact hne _ (setAt_elem hS x hx) (setAt_elem (c := denote α y) (inj := Value.num) hq x hx)
  · exact hne _ (setAt_elem hS x hx) (setAt_elem (c := denote α y) (inj := Value.bin) hq x hx)

/-- **Two primitives met at the bottom share no value.** -/
theorem Adm_prim_none : ∀ g g' : Ground, Ground.meet g g' = none →
    ∀ v, (Adm α (.prim g) v && Adm α (.prim g') v) = false
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

/-- The former class of a kind: the five scalar kinds are one class. -/
def Kind.former : Kind → Alg.Former
  | .string | .number | .boolean | .binary | .null => .prim
  | .set => .set
  | .array => .list
  | .map => .object

/-- The former class of an attribute: the class of its kind. -/
abbrev Attr.former (a : Attr) : Alg.Former := a.kind.former

/-- **The shape classes of DynamoDB.** A base or a literal writes and reads a scalar, `setCodec`
    writes and reads one of the three sets, and the prisms build `arr`, `l`, `map` and `m`. -/
noncomputable instance dynShapes : Alg.Shapes dynSyn where
  former := Attr.former
  formerA := Attr.former
  prim g v h := by
    have h' := (Alg.PrimAdm.admV_exact (S := dynSyn) g v).mpr h
    cases g with
    | base k => cases k <;> cases v <;> first | rfl | exact nomatch h'
    | literal k x =>
        cases k <;> cases v <;> first | rfl | simp [Alg.PrimAdm.admV, AdmLit, inL] at h'
  primA g a h := by
    have h' := (Alg.PrimAdm.admV_exact (S := dynSyn.op) g a).mpr h
    cases g with
    | base k => cases k <;> cases a <;> first | rfl | exact nomatch h'
    | literal k x => cases k <;> cases a <;> first | rfl | exact nomatch h'
  set L hL c v h := by
    cases hL
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp h
    rcases setCodec_f_eq.mp ha with ⟨S, rfl, -⟩ | ⟨S, rfl, -⟩ | ⟨S, rfl, -⟩ <;> rfl
  setA L hL c a h := by
    cases hL
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h
    rcases setCodec_f_eq.mp hw with ⟨S, rfl, -⟩ | ⟨S, rfl, -⟩ | ⟨S, rfl, -⟩ <;> rfl
  list L hL _ := by cases hL; rfl
  listA L hL _ := by cases hL; rfl
  map F hF _ := by cases hF; rfl
  mapA F hF _ := by cases hF; rfl

/-- The set former of DynamoDB: the set law of `setCodec`. -/
instance dynFormerAdm : Alg.FormerAdm dynSyn where
  set_never {_ β} _ _ h v := by
    obtain rfl : β = dynTableA := funext fun g => nomatch g
    exact Adm_set_and_false h v

/-- The leaves of DynamoDB keep apart what they meet at the bottom, on the write side. -/
instance dynLeafAdm : Alg.LeafAdm dynSyn where
  prim_none {_ β} g g' hp v := by
    obtain rfl : β = dynTableA := funext fun g => nomatch g
    exact Adm_prim_none g g' hp v

/-- The predicate leaves of DynamoDB hold together nowhere where they meet at the empty
    predicate. The store names no predicate but the truth, so no stored predicate meets. -/
instance dynLeafMeet : Alg.LeafMeet dynSig where
  pmeet_none
    | false, _, _, h, v => meetM_empty h v
    | true, _, _, h, _ => nomatch h

/-! ## DynamoDB is an instance of the laws, on the read side

`Alg.disjoint_soundA` proves the read side once, over any signature. DynamoDB supplies the read
law of its set former (`dynFormerAdmA`) and of its primitives (`dynLeafAdmA`). A literal reads
through its base's codec restricted, so two different literals at one base read nothing
together. -/

/-- Two terms that read only two different members share no attribute, so their conjunction is
    the bottom. This closes every row that answers `never` because the two read different `Attr`
    constructors. -/
theorem AdmA_and_false {x y : Term} {m m' : Member} (hne : m ≠ m')
    (hx : ∀ a, AdmA α x a = true → a.member = m) (hy : ∀ a, AdmA α y a = true → a.member = m')
    (a : Attr) : (AdmA α x a && AdmA α y a) = false := by
  refine Bool.eq_false_iff.mpr fun h => hne ?_
  rw [Bool.and_eq_true] at h
  exact (hx a h.1).symm.trans (hy a h.2)

/-- Where a literal reads, its base reads the same value: `literalCodec` is `baseCodec`
    restricted, and `Codec.restrict`'s `p` returns the base's own value where the guard passes. -/
theorem literal_p_base {k : GroundKind} {x : k.Carrier} {a : Attr} {v : Value}
    (h : (literalCodec k x).p a = some v) : (baseCodec k).p a = some v := by
  rw [literalCodec_p_restrict] at h
  simp only [Alg.restrict_p_def] at h
  cases hb : (baseCodec k).p a with
  | none => rw [hb] at h; simp at h
  | some w => rw [hb] at h; simp only [Option.bind] at h; split at h <;> simp_all

/-- Where a literal reads, its base reads: the literal's codec is the base's restricted. -/
theorem AdmA_base_of_literal {k : GroundKind} {x : k.Carrier} {bt : Term} {a : Attr}
    (hb : denote α bt = baseCodec k) (h : AdmA α (Term.literal k x) a = true) :
    AdmA α bt a = true := by
  refine (AdmA_exact bt a).mpr ?_
  rw [hb]
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp ((AdmA_exact _ a).mp h)
  rw [literal_p_base (show (literalCodec k x).p a = some w from hw)]
  rfl

/-- **A base reads only its own member.** -/
theorem AdmA_base_member (k : GroundKind) (a : Attr) (h : AdmA α (.base k) a = true) :
    a.member = k.member := by
  cases k <;> cases a <;> first | rfl | exact nomatch h

/-- **A literal reads only the member of its base**, because its base reads where it reads. -/
theorem AdmA_literal_member (k : GroundKind) (x : k.Carrier) (a : Attr)
    (h : AdmA α (.literal k x) a = true) : a.member = k.member :=
  AdmA_base_member k a (AdmA_base_of_literal rfl h)

/-- A literal's guard, read off a successful read: mirror of `literal_p_base`. -/
theorem literal_inL {k : GroundKind} {x : k.Carrier} {a : Attr} {v : Value}
    (h : (literalCodec k x).p a = some v) : inL k x v = true := by
  rw [literalCodec_p_restrict] at h
  simp only [Alg.restrict_p_def] at h
  cases hb : (baseCodec k).p a with
  | none => rw [hb] at h; simp at h
  | some w => rw [hb] at h; simp only [Option.bind] at h; split at h <;> simp_all

/-- **Two literals at one base and two values read nothing together.** Simp on `AdmLit` and
    `inL` does not reach the `number` row; exactness does. -/
theorem AdmA_literal_never_of_ne {k : GroundKind} {x y : k.Carrier} (hne : ¬ (x = y)) (a : Attr) :
    AdmA α (.never : Term) a = (AdmA α (Term.literal k x) a && AdmA α (Term.literal k y) a) := by
  cases hx : AdmA α (Term.literal k x) a with
  | false => simp [AdmA_rows]
  | true =>
      cases hy : AdmA α (Term.literal k y) a with
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
theorem AdmA_set_and_false {a y : Term} (h : ∀ u, (AdmA α a u && AdmA α y u) = false) (att : Attr) :
    (AdmA α (.set a) att && AdmA α (.set y) att) = false := by
  cases hA : AdmA α (.set a) att with
  | false => rfl
  | true =>
  cases hY : AdmA α (.set y) att with
  | false => rfl
  | true =>
  exfalso
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp ((AdmA_exact _ att).mp hA)
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp ((AdmA_exact _ att).mp hY)
  have hne : ∀ w, ((denote α a).p w).isSome = true → ((denote α y).p w).isSome = true → False :=
    fun w h1 h2 => by
      have := h w
      rw [(AdmA_exact a w).mpr h1, (AdmA_exact y w).mpr h2] at this
      exact Bool.noConfusion this
  rcases setCodec_f_eq.mp hp with ⟨S, rfl, hS⟩ | ⟨S, rfl, hS⟩ | ⟨S, rfl, hS⟩ <;>
    obtain ⟨x, hx⟩ := S.2
  · exact hne _ (setAt_elem hS x hx) (setAt_elem (c := denote α y) (inj := Attr.s) hq x hx)
  · exact hne _ (setAt_elem hS x hx) (setAt_elem (c := denote α y) (inj := Attr.n) hq x hx)
  · exact hne _ (setAt_elem hS x hx) (setAt_elem (c := denote α y) (inj := Attr.b) hq x hx)

/-- **Two primitives met at the bottom read nothing together.** -/
theorem admA_prim_none : ∀ g g' : Ground, Ground.meet g g' = none →
    ∀ a, (AdmA α (.prim g) a && AdmA α (.prim g') a) = false
  | .base k, .base k', hp, a => by
      simp only [Ground.meet] at hp
      split at hp
      · exact nomatch hp
      · next hk =>
          exact AdmA_and_false
            (by cases k <;> cases k' <;> first | exact absurd rfl hk | decide)
            (AdmA_base_member k) (AdmA_base_member k') a
  | .base k, .literal k' x, hp, a => by
      simp only [Ground.meet] at hp
      split at hp
      · exact nomatch hp
      · next hk =>
          exact AdmA_and_false
            (by cases k <;> cases k' <;> first | exact absurd rfl hk | decide)
            (AdmA_base_member k) (AdmA_literal_member k' _) a
  | .literal k x, .base k', hp, a => by
      simp only [Ground.meet] at hp
      split at hp
      · exact nomatch hp
      · next hk =>
          exact AdmA_and_false
            (by cases k <;> cases k' <;> first | exact absurd rfl hk | decide)
            (AdmA_literal_member k _) (AdmA_base_member k') a
  | .literal k x, .literal k' x', hp, a => by
      simp only [Ground.meet] at hp
      cases k <;> cases k' <;> simp only [Ground.meetLit, reduceCtorEq] at hp <;>
        (try split at hp) <;>
        first
          | (simp only [reduceCtorEq] at hp; done)
          | exact AdmA_and_false (by decide) (AdmA_literal_member _ _)
              (AdmA_literal_member _ _) a
          | (rename_i hne; rw [← AdmA_literal_never_of_ne hne a]; rfl)

/-- The set former of DynamoDB, on the read side. -/
instance dynFormerAdmA : Alg.FormerAdmA dynSyn where
  set_never {β _} _ _ h c := by
    obtain rfl : β = dynTableA := funext fun g => nomatch g
    exact AdmA_set_and_false h c

/-- The primitives of DynamoDB keep apart what they meet at the bottom, on the read side. -/
instance dynLeafAdmA : Alg.LeafAdmA dynSyn where
  prim_none {β _} g g' hp c := by
    obtain rfl : β = dynTableA := funext fun g => nomatch g
    exact admA_prim_none g g' hp c


/-! ## The views admit what the term admits -/

mutual
/-- **The view holds no `held`.** Each `held` becomes its view, and a refinement that the view
    keeps as it is has an inner term with no `held`. -/
theorem HF_view (o : Orient) : ∀ t : Term, HF (view o t)
  | .held s t P _ _ => by
      simp only [view]; cases s == o.c
      exacts [HF_view o t, HF_view o P]
  | .refine t _ _ => by
      simp only [view]
      split
      · cases o.c
        · exact HF_view o t
        · exact HF_view o t
      · next h =>
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h
        exact h.1
  | .list pre sp suf => by
      simp only [view, HF, hasHeld, Bool.or_eq_false_iff]
      exact ⟨⟨HF_viewL o pre, HF_viewO o sp⟩, HF_viewL o suf⟩
  | .object (.mk fs f w) => by
      simp only [view, viewB, HF, hasHeld, Alg.hasHeldB, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_exists]
      exact ⟨fun k => Bool.eq_false_iff.mp (HF_viewS o (f k)), HF_viewO o w⟩
  | .union os => by simp only [view]; exact HF_viewL o os
  | .set t => by simp only [view]; exact HF_view o t
  | .mu b => by simp only [view]; exact HF_view o b
  | .prim _ => rfl | .opaq => rfl | .never => rfl | .var _ => rfl
/-- `HF_view` over a list. -/
theorem HF_viewL (o : Orient) : ∀ ts : List Term, HFL (viewL o ts)
  | [] => rfl
  | t :: ts => by
      simp only [viewL, HFL, Alg.hasHeldL, Bool.or_eq_false_iff]; exact ⟨HF_view o t, HF_viewL o ts⟩
/-- `HF_view` at an optional term. -/
theorem HF_viewO (o : Orient) : ∀ x : Option Term, HFO (viewO o x)
  | none => rfl
  | some t => HF_view o t
/-- `HF_view` at a slot. -/
theorem HF_viewS (o : Orient) : ∀ s : ObjectSlot, HFS (viewS o s)
  | .req t => HF_view o t
  | .optional t => HF_view o t
end

/-- A union of rows over wider rows admits where the narrower union admits. -/
theorem anyP_mono {α : Type} : ∀ {Ps Qs : List (α → Bool)}, List.Forall₂ RowLe Ps Qs →
    ∀ x, anyP Ps x = true → anyP Qs x = true
  | [], [], .nil, _, h => h
  | _ :: _, _ :: _, .cons hPQ hr, x, h => by
      simp only [anyP, Bool.or_eq_true] at h ⊢
      exact h.imp (hPQ x) (anyP_mono hr x)

/-- **A set over a restriction of `Ω` acts, at the orientation, where a set over a narrower
    element acts.** -/
theorem setCodec_mono (o : Orient) {c d : Codec} (hd : Sub d Ω)
    (h : ∀ w, (c.f o w).isSome = true → (d.f o w).isSome = true) (x : Attr)
    (hx : ((setCodec c).f o x).isSome = true) : ((setCodec d).f o x).isSome = true := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hx
  refine (setCodec_isSome_of_sub hd o x).mpr ?_
  rcases setCodec_f_eq.mp ha with ⟨S, rfl, hS⟩ | ⟨S, rfl, hS⟩ | ⟨S, rfl, hS⟩ <;>
    exact fun y hy => h _ (setAt_elem hS y hy)

/-- The second environment acts, at each index and at the orientation, where the first acts. -/
def EnvLe (o : Orient) (ρ ρ' : List Codec) : Prop :=
  ∀ i x, ((Alg.envAt ρ i).f o x).isSome = true → ((Alg.envAt ρ' i).f o x).isSome = true
/-- Each codec of the environment is a restriction of `Ω`. -/
def EnvSub (ρ : List Codec) : Prop := ∀ i, Sub (Alg.envAt ρ i) Ω

/-- A codec that acts more, on top of an environment that acts more. -/
theorem EnvLe.cons {o : Orient} {c c' : Codec} {ρ ρ' : List Codec}
    (hc : ∀ x, (c.f o x).isSome = true → (c'.f o x).isSome = true) (h : EnvLe o ρ ρ') :
    EnvLe o (c :: ρ) (c' :: ρ')
  | 0 => hc
  | i + 1 => h i
/-- A restriction of `Ω`, on top of an environment of restrictions of `Ω`. -/
theorem EnvSub.cons {c : Codec} {ρ : List Codec} (hc : Sub c Ω) (h : EnvSub ρ) : EnvSub (c :: ρ)
  | 0 => hc
  | i + 1 => h i
/-- The empty environment gives the bottom at each index. -/
theorem EnvSub.nil : EnvSub [] := fun _ => Alg.sub_empty

/-- The entry test of an object over wider slot rows and a wider open block admits where the
    narrower test admits. -/
theorem objAdmV_mono {α : Type} {fs : Finset Name} {P Q : {k // k ∈ fs} → α → Bool}
    {wP wQ : Option (α → Bool)} (hf : ∀ k, RowLe (P k) (Q k)) (hw : Option.Rel RowLe wP wQ)
    {keys : Finset Name} {g : {k // k ∈ keys} → α}
    (h : objAdmV ⟨fs, P⟩ wP keys g = true) : objAdmV ⟨fs, Q⟩ wQ keys g = true := by
  unfold objAdmV at h ⊢
  refine decide_eq_true fun k => ?_
  have := of_decide_eq_true h k
  rcases Decidable.em (k.1 ∈ fs) with hm | hm
  · simp only [entryP, MapOf.at, dif_pos hm] at this ⊢
    exact hf ⟨k.1, hm⟩ _ this
  · simp only [entryP, MapOf.at, dif_neg hm] at this ⊢
    cases hw with
    | none => exact this
    | some hr => exact hr _ this

section
variable (o : Orient) [Alg.PrimAdm ⟨dynSig, o⟩] (α : Alg.Table ⟨dynSig, o⟩)
  (β : Alg.Table (Alg.Syn.op ⟨dynSig, o⟩))

mutual
/-- **The view admits at the orientation each value that the term admits**, under an
    environment that acts at each index where the first environment acts. One proof serves both
    orientations: the value side at the host, and the attribute side at the dual.

    The environment is what the `mu` row needs. A recursive term admits what its body admits over
    the stage below the depth of the value (`Adm_mu_unfold`), and the view does the same over the
    stage of the view. An induction over the stages carries the inclusion to each stage. The
    environment of the view is a restriction of `Ω`, because the view holds no `held`, and the
    `set` row reads a restriction of `Ω` element by element.

    A `held` and a refinement over a possible `held` are the two rows that read the orientation.
    A refinement that the view keeps as it is has an inner term with no variable, so the
    environment does not change its map (`denote_closed`). -/
theorem viewLeE : ∀ (t : Term) (ρ ρ' : List Codec), EnvLe o ρ ρ' → EnvSub ρ' →
    RowLe (Alg.Adm α β t ρ) (Alg.Adm α β (view o t) ρ')
  | .held true _ _ k₀ _, _, _, _, _ => nomatch k₀.1
  | .held false t P _ _, ρ, ρ', he, hs => by
      have ihP := viewLeE P ρ ρ' he hs
      have iht := viewLeE t ρ ρ' he hs
      revert ihP iht
      rcases o with ⟨⟨_ | _, _ | _⟩, ho⟩
      · exact absurd rfl ho
      · exact fun ihP _ v h => ihP v (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2
      · exact fun _ iht v h => iht v (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1
      · exact absurd rfl ho
  | .var i, _, _, he, _ => fun v h => by
      rw [Alg.Adm_eq_isSome] at h ⊢
      exact he i v h
  | .mu b, ρ, ρ', he, hs => fun v h => by
      simp only [view]
      rw [Alg.Adm_mu_unfold] at h ⊢
      have hst : ∀ n, (∀ w, ((Alg.muStage (fun c => Alg.denote α β b (c :: ρ)) n).f o w).isSome = true →
          ((Alg.muStage (fun c => Alg.denote α β (view o b) (c :: ρ')) n).f o w).isSome = true) ∧
          Sub (Alg.muStage (fun c => Alg.denote α β (view o b) (c :: ρ')) n) Ω := by
        intro n
        induction n with
        | zero => exact ⟨(fun _ hw => nomatch hw), Alg.sub_empty⟩
        | succ n ih =>
          have he' := EnvLe.cons ih.1 he
          have hs' := EnvSub.cons ih.2 hs
          refine ⟨fun w hw => ?_, Alg.sub_denoteIn (α := α) (β := β) (view o b) (HF_view o b) _ hs'⟩
          have := viewLeE b _ _ he' hs' w (by rw [Alg.Adm_eq_isSome]; exact hw)
          rwa [Alg.Adm_eq_isSome] at this
      exact viewLeE b _ _ (EnvLe.cons (hst _).1 he) (EnvSub.cons (hst _).2 hs) v h
  | .refine t p pA, ρ, ρ', he, hs => by
      simp only [view]
      split
      · have iht := viewLeE t ρ ρ' he hs
        revert iht
        rcases o with ⟨⟨_ | _, _ | _⟩, ho⟩
        · exact absurd rfl ho
        · refine fun iht v h => ?_
          have h' := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1
          have hw := iht v h'.1
          refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨hw, h'.2⟩, ?_⟩
          rw [Alg.Adm_eq_isSome] at hw
          exact (Alg.gate_true _ _).trans hw
        · exact fun iht v h => iht v (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1
        · exact absurd rfl ho
      · next hv =>
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hv
        intro v h
        rw [Alg.Adm_eq_isSome] at h ⊢
        rwa [Alg.denote_closed (α := α) (β := β) (.refine t p pA) hv.2 ρ' ρ]
  | .list pre sp suf, ρ, ρ', he, hs => fun v h => by
      cases hl : Alg.listOut (S := ⟨dynSig, o⟩) v with
      | none => rw [Alg.Adm_list_of_none hl] at h; exact absurd h Bool.false_ne_true
      | some vs =>
        rw [Alg.Adm_list_of_out hl] at h
        simp only [view]; rw [Alg.Adm_list_of_out hl]
        exact alignPL_mono (viewLeEL pre ρ ρ' he hs) (viewLeEO sp ρ ρ' he hs)
          (viewLeEL suf ρ ρ' he hs) vs h
  | .object (.mk fs f w), ρ, ρ', he, hs => fun v h => by
      change Alg.AdmBody α β (.mk fs f w) ρ v = true at h
      change Alg.AdmBody α β (.mk fs (fun k => viewS o (f k)) (viewO o w)) ρ' v = true
      cases hm : Alg.mapOut (S := ⟨dynSig, o⟩) v with
      | none => rw [Alg.AdmBody_of_none hm] at h; exact absurd h Bool.false_ne_true
      | some m =>
        rw [Alg.AdmBody_of_out hm] at h; rw [Alg.AdmBody_of_out hm]
        simp only [Alg.Body.fields_mk, Alg.Body.at_mk, Alg.Body.wild_mk] at h ⊢
        rw [Bool.and_eq_true] at h ⊢
        refine ⟨?_, objAdmV_mono (fun k => viewLeES (f k) ρ ρ' he hs) ?_ h.2⟩
        · refine decide_eq_true fun k => ?_
          have := of_decide_eq_true h.1 k
          beta_reduce
          generalize f k = s at this ⊢
          cases s <;> simp_all [viewS]
        · cases w with
          | none => exact .none
          | some t => exact .some (viewLeE t ρ ρ' he hs)
  | .union os, ρ, ρ', he, hs => fun v h => anyP_mono (viewLeEL os ρ ρ' he hs) v h
  | .set t, ρ, ρ', he, hs => fun v h => by
      simp only [view]
      rw [Alg.Adm_eq_isSome] at h ⊢
      exact setCodec_mono o (c := Alg.denote α β t ρ)
        (Alg.sub_denoteIn (α := α) (β := β) _ (HF_view o t) ρ' hs)
        (fun w hw => by
          have := viewLeE t ρ ρ' he hs w (by rw [Alg.Adm_eq_isSome]; exact hw)
          rwa [Alg.Adm_eq_isSome] at this) v h
  | .prim _, _, _, _, _ => fun _ h => h
  | .opaq, _, _, _, _ => fun _ h => h
  | .never, _, _, _, _ => fun _ h => h
/-- `viewLeE` over a list. -/
theorem viewLeEL : ∀ (ts : List Term) (ρ ρ' : List Codec), EnvLe o ρ ρ' → EnvSub ρ' →
    List.Forall₂ RowLe (Alg.AdmList α β ts ρ) (Alg.AdmList α β (viewL o ts) ρ')
  | [], _, _, _, _ => .nil
  | t :: ts, ρ, ρ', he, hs => .cons (viewLeE t ρ ρ' he hs) (viewLeEL ts ρ ρ' he hs)
/-- `viewLeE` at an optional term. -/
theorem viewLeEO : ∀ (x : Option Term) (ρ ρ' : List Codec), EnvLe o ρ ρ' → EnvSub ρ' →
    Option.Rel RowLe (Alg.AdmOptT α β x ρ) (Alg.AdmOptT α β (viewO o x) ρ')
  | none, _, _, _, _ => .none
  | some t, ρ, ρ', he, hs => .some (viewLeE t ρ ρ' he hs)
/-- `viewLeE` at a slot. -/
theorem viewLeES : ∀ (s : ObjectSlot) (ρ ρ' : List Codec), EnvLe o ρ ρ' → EnvSub ρ' →
    RowLe (Alg.AdmField α β s ρ) (Alg.AdmField α β (viewS o s) ρ')
  | .req t, ρ, ρ', he, hs => viewLeE t ρ ρ' he hs
  | .optional t, ρ, ρ', he, hs => viewLeE t ρ ρ' he hs
end

/-- **The view admits at the orientation each value that the term admits.** -/
theorem viewLe_of (t : Term) : RowLe (Alg.Adm α β t []) (Alg.Adm α β (view o t) []) :=
  viewLeE o α β t [] [] (fun _ _ h => h) EnvSub.nil

end


/-! ## The orthogonal row -/

/-- **Orthogonal terms admit no common value.** A value that both terms admit is admitted by
    both caller views, and the views are disjoint. -/
theorem viewsDisjoint_adm {x y : Term} (h : viewsDisjoint x y = true) (v : Value) :
    (Adm α x v && Adm α y v) = false := by
  simp only [viewsDisjoint, Bool.and_eq_true] at h
  have hw := Alg.disjoint_sound (α := α) (β := dynTableA) pair0 _ _ h.1 [] [] (fun _ _ _ hp => nomatch hp) v
  cases hx : Adm α x v <;> cases hy : Adm α y v <;> simp only [Bool.and_false, Bool.false_and, Bool.and_self]
  have e1 : Alg.Adm α dynTableA (view .host x) [] v = true := viewLe_of .host α dynTableA x v hx
  have e2 : Alg.Adm α dynTableA (view .host y) [] v = true := viewLe_of .host α dynTableA y v hy
  rw [e1, e2] at hw; exact nomatch hw

/-- **Orthogonal terms read no common attribute.** An attribute that both terms read is read
    by both stored views, and the views are disjoint. -/
theorem viewsDisjoint_admA {x y : Term} (h : viewsDisjoint x y = true) (a : Attr) :
    (AdmA α x a && AdmA α y a) = false := by
  simp only [viewsDisjoint, Bool.and_eq_true] at h
  have hr := Alg.disjoint_soundA (α := α) (β := dynTableA) pair0 _ _ h.2 [] [] (fun _ _ _ hp => nomatch hp) a
  cases hx : AdmA α x a <;> cases hy : AdmA α y a <;> simp only [Bool.and_false, Bool.false_and, Bool.and_self]
  have e1 : Alg.AdmA α dynTableA (view .dual x) [] a = true := viewLe_of .dual dynTableA α x a hx
  have e2 : Alg.AdmA α dynTableA (view .dual y) [] a = true := viewLe_of .dual dynTableA α y a hy
  rw [e1, e2] at hr; exact nomatch hr

/-- **The pair certificate is sound**: orthogonality separates the pair. -/
theorem separates_of_certPair {x y : Term} (h : certPair x y = true) : Separates α x y := by
  refine ⟨fun v hx hy => ?_, fun a hx hy => ?_⟩
  · have := viewsDisjoint_adm (α := α) h v
    rw [hx, hy] at this; exact nomatch this
  · have := viewsDisjoint_admA (α := α) h a
    rw [hx, hy] at this; exact nomatch this

/-- **The certificate refuses a pair that only the model's caller carrier separates.** Each option
    is a set of adapters, and each caller side admits a boolean. The host builds `Set([true])` as
    a caller value of each option, and the two options write that value to `SS` and to `NS`. So
    the host refuses the union. The model's `Value` has no set of booleans, so in the model the
    two options write disjoint slots. The caller sides share `boolean`, so the caller views are
    not disjoint, and the certificate agrees with the host. -/
example :
    certPair (.set (.refine (.held false .string (.union [.string, .boolean]) (.caller 0, false) [])
        (.closure fun _ => true) ()))
      (.set (.held false .number (.union [.number, .boolean]) (.caller 1, false) [])) = false := by
  decide

/-- **The certificate refuses a separated pair at a data predicate over a variable.** The pair is
    separated: `mu (refine (union [string, array (var 0)]) {a})` admits the string `"a"` and no
    other string, and `refine string {b}` admits the string `"b"` alone. The test compares two
    data predicates only over closed held-free inner terms, and this inner term holds a variable.
    So `certPair` answers `false`. The host builds no data predicate over a variable, so no
    observable distinguishes this test from a finer test. A finer test becomes necessary only
    when the host builds such a term. -/
example :
    certPair (.mu (.refine (.union [.string, .array (.var 0)]) (.members .string (NEFinset.of "a" ∅)) ()))
        (.refine .string (.members .string (NEFinset.of "b" ∅)) ()) = false := by
  decide

/-- **A certified union is separated**, which is the premise of `pairwiseCompat_of_separated`
    and of `admitsAtMostOne_of_separated`. -/
theorem separated_of_unionOk {os : List Term} (h : unionOk os = true) : Separated α os :=
  (pairwise_of_certAll h).imp separates_of_certPair


end Calculus
