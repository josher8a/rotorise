import Calculus.HeldSet
import Calculus.Merge
import Calculus.Orthogonality
import Calculus.Laminar

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
at all (`never`) and a term that names no *single* stored member (`union`, `opaq`, `lazy`,
`lazy`) — so a factor answering `none` constrains nothing. The two examples at the foot of this
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

**A union carries a certificate, and the meet reads it.** `Adm (.union os)` is `selOptV`, which
admits where *exactly one* option admits structurally. That is the join of the options' admissions
only when the options carry `unionOk`: each pair passes `Orth` or meets at the bottom, so no value
is refused for being admitted twice. Each option's structural test is its row whether or not the option is open, because the
structural lemmas read the open block. Without the certificate the meet has nothing to state.

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


/-! ## Reading a field and a term -/

/-- Whether a slot admits nothing at a name that must be present. An `optional` slot at the
    bottom is not this: it is a name that must be absent, which is a body a value can satisfy. -/
def ObjectSlot.isBottom : ObjectSlot → Bool
  | .req t => t.isNever
  | .optional _ => false

/-- Whether a predicate is data a term can carry through a meet. `closure` is the caller's own
    function and is the one case `Pred` keeps open. -/
def Pred.isData : Pred → Bool
  | .closure _ => false
  | _ => true

/-- A union of what survived a distribution: nothing is the bottom, one survivor is itself, and
    the rest are a union again. -/
def Term.ofOptions : List Term → Term
  | [] => .never
  | [t] => t
  | ts => .union ts

/-- A list of answers, as one answer: `none` where any cell refused. Outside the recursion, so
    the rows below reach a list through `List.attach` and a `map` rather than through a mutual
    companion — which is what makes every recursive call strictly shallower in one measure. -/
def allSome {α : Type} : List (Option α) → Option (List α)
  | [] => some []
  | none :: _ => none
  | some x :: rest => (allSome rest).map (x :: ·)

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

/-- The meet of two element predicates, lifted to `each`. -/
def Pred.meetEach : Option (Option Pred) → Option (Option Pred)
  | some (some r) => some (some (.each r))
  | some none => some none
  | none => none

/-- **Two predicates, met.** `none` is a refusal to combine, `some none` says that no value
    satisfies both, and `some (some r)` is the combined predicate. Every data case meets every
    data case: `members` and `except` at any two bases, and `each` with `each` through the meet
    of the element predicates. A scalar predicate and `each` share no value, because `each`
    holds only a set. A `closure` refuses, because nothing reads a caller's function. -/
def Pred.meetM : Pred → Pred → Option (Option Pred)
  | .members k A, .members k' B => Pred.meetMem k A k' B
  | .members k A, .except k' B  => Pred.meetMemExc k A k' B
  | .except k B,  .members k' A => Pred.meetMemExc k' A k B
  | .except k A,  .except k' B  => Pred.meetExc k A k' B
  | .each p, .each q => Pred.meetEach (Pred.meetM p q)
  | .members _ _, .each _ => some none
  | .except _ _,  .each _ => some none
  | .each _, .members _ _ => some none
  | .each _, .except _ _  => some none
  | _, _ => none

/-- **A refinement over the bottom is the bottom, and two refinements over one carrier meet.**
    The bottom bubbles up through a slot that must hold a value, and a refinement's inner term
    is one. A second refinement over an already-refined term does not stack: the predicates meet,
    and where they share no alternative the result is the bottom. Without that second case, a
    refinement whose predicate holds of nothing the inner term holds is empty and is not spelled
    `never`. Called
    from both refinement rows of the meet, so every refinement the meet builds is normal. -/
def Term.refineOf (z : Term) (p : Pred) : Term :=
  match z with
  | .never => .never
  | .refine z' q =>
      match Pred.meetM q p with
      | some (some r) => .refine z' r
      | some none     => .never
      | none          => .refine (.refine z' q) p
  | _ => .refine z p

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

/-- A scalar base holds no set, and `each` holds nothing else. -/
theorem liftQ_false_of_base {k : GroundKind} {v : Value} (h : inBase k v = true) (q : Value → Bool) :
    liftQ q v = false := by
  cases k <;> cases v <;> first | rfl | exact nomatch h

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

/-- `each` lifts a conjunction to a conjunction. -/
theorem liftQ_and (p q : Value → Bool) (v : Value) :
    liftQ (fun w => p w && q w) v = (liftQ p v && liftQ q v) := by
  cases v <;> simp only [liftQ] <;>
    first
      | rfl
      | (refine Bool.eq_iff_iff.mpr ?_
         simp only [Bool.and_eq_true, decide_eq_true_eq]
         exact ⟨fun h => ⟨fun s hs => (h s hs).1, fun s hs => (h s hs).2⟩,
           fun h s hs => ⟨h.1 s hs, h.2 s hs⟩⟩)

/-- **No set has every element in an empty meet**, because a wire set is not empty. -/
theorem liftQ_and_false {p q : Value → Bool} (h : ∀ w, (p w && q w) = false) (v : Value) :
    (liftQ p v && liftQ q v) = false := by
  rw [← liftQ_and]
  cases v with
  | strSet S =>
    obtain ⟨s, hs⟩ := S.2
    exact decide_eq_false (fun hall => Bool.false_ne_true ((h _).symm.trans (hall s hs)))
  | numSet S =>
    obtain ⟨s, hs⟩ := S.2
    exact decide_eq_false (fun hall => Bool.false_ne_true ((h _).symm.trans (hall s hs)))
  | binSet S =>
    obtain ⟨s, hs⟩ := S.2
    exact decide_eq_false (fun hall => Bool.false_ne_true ((h _).symm.trans (hall s hs)))
  | _ => rfl

/-- `each` meets `each` through the meet of the element predicates. -/
theorem meetEach_ok {p q : Pred} :
    ∀ {o : Option (Option Pred)}, MeetOk p q o → MeetOk (.each p) (.each q) (Pred.meetEach o)
  | some (some r), h => fun v => by
      show liftQ r.eval v = (liftQ p.eval v && liftQ q.eval v)
      rw [← liftQ_and, show r.eval = fun w => p.eval w && q.eval w from funext h]
  | some none, h => fun v => liftQ_and_false h v
  | none, _ => trivial

/-- A scalar `members` and an `each` share no value, because `each` holds only a set. -/
theorem members_each_ok (k : GroundKind) (A : NEFinset k.Carrier) (q : Pred) :
    MeetOk (.members k A) (.each q) (some none) := by
  intro v
  show (inLs k A v && liftQ q.eval v) = false
  cases hk : inBase k v with
  | false => rw [inLs_false_of_base hk]; rfl
  | true => rw [liftQ_false_of_base hk, Bool.and_false]

/-- An `except` and an `each` share no value, because `except` holds only a scalar. -/
theorem except_each_ok (k : GroundKind) (A : NEFinset k.Carrier) (q : Pred) :
    MeetOk (.except k A) (.each q) (some none) := by
  intro v
  show ((inBase k v && !inLs k A v) && liftQ q.eval v) = false
  cases hk : inBase k v with
  | false => rfl
  | true => rw [liftQ_false_of_base hk, Bool.and_false]

/-- **The predicate meet is sound at every row.** -/
theorem meetM_ok : ∀ q p : Pred, MeetOk q p (Pred.meetM q p)
  | .members k A, .members k' B => meetMem_ok k A k' B
  | .members k A, .except k' B  => meetMemExc_ok k A k' B
  | .except k B,  .members k' A => (meetMemExc_ok k' A k B).symm
  | .except k A,  .except k' B  => meetExc_ok k A k' B
  | .each p, .each q => meetEach_ok (meetM_ok p q)
  | .members k A, .each q => members_each_ok k A q
  | .except k A,  .each q => except_each_ok k A q
  | .each q, .members k A => (members_each_ok k A q).symm
  | .each q, .except k A  => (except_each_ok k A q).symm
  | .members _ _, .closure _ => trivial
  | .except _ _,  .closure _ => trivial
  | .each _,      .closure _ => trivial
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


/-- **A list with a declared position at the bottom is the bottom.** Every value the list
    admits fills each declared position, so one position holding nothing empties the list.
    The SPREAD is not such a slot: a value of exactly the declared length omits every spread
    position, so a spread at the bottom reads "exactly the declared positions" rather than
    "nothing". The prefix and the suffix are both declared; the spread is not. -/
def Term.listOf (pre : List Term) (sp : Option Term) (suf : List Term) : Term :=
  if pre.any Term.isNever || suf.any Term.isNever then .never else .list pre sp suf

/-- The suffix-free case, under the name the tuple rows use. -/
def Term.tupleOf (ts : List Term) (tail : Option Term) : Term :=
  Term.listOf ts tail []

/-- A normalised list is a list or the bottom. -/
theorem listOf_cases (pre : List Term) (sp : Option Term) (suf : List Term) :
    Term.listOf pre sp suf = .never ∨ Term.listOf pre sp suf = .list pre sp suf := by
  unfold Term.listOf; split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-! ## The meet -/

mutual

/-- Two literals: the same value at the same base, or nothing.

    `number` refuses, and the reason it used to carry is gone: its equality came from an
    axiomatised host, and the exact carrier decides. The refusal stands with no stated reason, and a row would be a change to the
    meet rather than a repair. -/
def Term.meetLit : (k : GroundKind) → k.Carrier → (k' : GroundKind) → k'.Carrier → Option Term
  | .string, v, .string, v' => if v = v' then some (.literal .string v) else some .never
  | .boolean, v, .boolean, v' => if v = v' then some (.literal .boolean v) else some .never
  | .binary, v, .binary, v' => if v = v' then some (.literal .binary v) else some .never
  -- `Unit` has one inhabitant, so two null literals name the same value
  | .null, v, .null, _ => some (.literal .null v)
  | .number, _, .number, _ => none
  | _, _, _, _ => some .never


end

/-! ## The meet, structurally

Every row keeps the left operand on the left. -/

def zipF : List (Term → Option Term) → List Term → List (Option Term)
  | [], _ => [] | _, [] => []
  | f :: fs, u :: us => f u :: zipF fs us

mutual
/-- **Every row that reads the right operand alone, written once.** The bottom, the four whose
    admission is a function, a thunk, a refinement and a certified union answer the same way
    whatever the left operand is, so they are stated here rather than restated per left
    constructor. `lazy` is transparent: the row meets the left operand with the subterm, because
    `Adm (.lazy t) = Adm t` and `AdmA (.lazy t) = AdmA t`. `fam` carries the left operand,
    already applied. -/
def meetSRight (fam : Term → Option Term) : Term → Option Term
  | .never => some .never
  | .held _ _ _ _ => none
  | .lazy t => meetSRight fam t
  | .refine y p => if p.isData then (meetSRight fam y).map (fun z => Term.refineOf z p) else none
  | .union os => (allSome (meetSRightL fam os)).bind
      (fun zs => some (Term.ofOptions (zs.filter (fun z => !z.isNever))))
  | y => fam y
def meetSRightL (fam : Term → Option Term) : List Term → List (Option Term)
  | [] => [] | y :: ys => meetSRight fam y :: meetSRightL fam ys
end

/-! ### The families: one per left constructor, flat and non-recursive. -/
def famString : Term → Option Term
  | .string => some .string
  | .literal k v => match k, v with
      | .string, v => some (.literal .string v) | _, _ => some .never
  | .opaq => some .string
  | _ => some .never

def famNumber : Term → Option Term
  | .number => some .number
  | .literal k v => match k, v with
      | .number, v => some (.literal .number v) | _, _ => some .never
  | .opaq => some .number
  | _ => some .never

def famBoolean : Term → Option Term
  | .boolean => some .boolean
  | .literal k v => if k = .boolean then some (.literal k v) else some .never
  | .opaq => some .boolean
  | _ => some .never

def famBinary : Term → Option Term
  | .binary => some .binary
  | .literal k v => if k = .binary then some (.literal k v) else some .never
  | .opaq => some .binary
  | _ => some .never

def famNull : Term → Option Term
  | .null => some .null
  | .literal k v => if k = .null then some (.literal k v) else some .never
  | .opaq => some .null
  | _ => some .never

def famLit (k : GroundKind) (v : k.Carrier) : Term → Option Term
  | .string => match k, v with
      | .string, v => some (.literal .string v) | _, _ => some .never
  | .number => match k, v with
      | .number, v => some (.literal .number v) | _, _ => some .never
  | .boolean => if k = .boolean then some (.literal k v) else some .never
  | .binary => if k = .binary then some (.literal k v) else some .never
  | .null => if k = .null then some (.literal k v) else some .never
  | .literal k' v' => Term.meetLit k v k' v'
  | .opaq => none
  | _ => some .never

def famSet (b : SetBase) : Term → Option Term
  | .set b' => if b = b' then some (.set b) else some .never
  | .opaq => none
  | _ => some .never

def famOpaq : Term → Option Term
  | .string => some .string
  | .boolean => some .boolean
  | .binary => some .binary
  | .null => some .null
  | .number => some .number
  | .opaq => some .opaq
  | _ => none

/-- **The row a `list` shape assigns to `n` positions**: the prefix, the spread as often as
    the middle needs, then the suffix. `none` is the length the shape refuses. One
    definition serves both operands, because the left operand's positions are partially
    applied meets and the right operand's are terms, and the shape does not care which.
    Mirrors `slotsL` one level up. -/
def rowOfG {α : Type} (pre : List α) (sp : Option α) (suf : List α) (n : Nat) :
    Option (List α) :=
  match sp with
  | some c =>
      if n < pre.length + suf.length then none
      else some (pre ++ List.replicate (n - pre.length - suf.length) c ++ suf)
  | none => if n = pre.length + suf.length then some (pre ++ suf) else none

/-- The spread row, split at the suffix. Stated over an explicit split so no rewrite has to
    reach inside a length. -/
theorem zipP_row_split (pre suf : List VP) (c : VP) (A B : List Value)
    (hB : B.length = suf.length) (hA : pre.length ≤ A.length) :
    (zipP (pre ++ List.replicate (A.length - pre.length) c) A && zipP suf B)
      = zipP (pre ++ List.replicate ((A ++ B).length - pre.length - suf.length) c ++ suf)
          (A ++ B) := by
  have hcount : (A ++ B).length - pre.length - suf.length = A.length - pre.length := by
    simp only [List.length_append, hB]; omega
  rw [hcount, zipP_append _ _ _ _
      (by simp only [List.length_append, List.length_replicate]; omega)]

/-- **`alignPL` is its row, applied position for position.** This is `align_eq_zip` one level
    down, and it is what lets the meet reason about two shapes by reasoning about their rows
    at one length: the admission of a `list` at a value of length `n` is the admission of the
    row `rowOfG` assigns to `n`, position by position. -/
theorem alignPL_eq_rowOfG (pre : List VP) (sp : Option VP) (suf : List VP) (ws : List Value) :
    alignPL pre sp suf ws
      = match rowOfG pre sp suf ws.length with
        | none => false
        | some row => zipP row ws := by
  have htl : (ws.take (ws.length - suf.length)).length = ws.length - suf.length := by
    simp only [List.length_take]; omega
  unfold alignPL
  rcases Nat.lt_or_ge ws.length (pre.length + suf.length) with hlt | hge
  · have hrow : rowOfG pre sp suf ws.length = none := by
      cases sp with
      | none => simp only [rowOfG]; rw [if_neg (by omega)]
      | some c => simp only [rowOfG]; rw [if_pos (by omega)]
    rw [hrow]
    rcases Nat.lt_or_ge ws.length suf.length with hs | hs
    · rw [zipP_false_of_length_ne _ _ (by simp only [List.length_drop]; omega), Bool.and_false]
    · rw [alignP_short _ _ _ (by omega), Bool.false_and]
  · have hdl : (ws.drop (ws.length - suf.length)).length = suf.length := by
      simp only [List.length_drop]; omega
    have hAB : ws.take (ws.length - suf.length) ++ ws.drop (ws.length - suf.length) = ws :=
      List.take_append_drop _ _
    cases sp with
    | none =>
        rw [alignP_none_eq_zipP]
        simp only [rowOfG]
        rcases Nat.eq_or_lt_of_le hge with heq | hlt2
        · rw [if_pos heq.symm]
          show _ = zipP (pre ++ suf) ws
          have hz := (zipP_append pre suf (ws.take (ws.length - suf.length))
            (ws.drop (ws.length - suf.length)) (by omega)).symm
          rw [hAB] at hz
          exact hz
        · rw [if_neg (by omega)]
          show _ = false
          rw [zipP_false_of_length_ne _ _ (by omega), Bool.false_and]
    | some c =>
        rw [alignP_some_eq_zipP _ _ _ (by omega)]
        simp only [rowOfG]
        rw [if_neg (by omega)]
        show _ = zipP (pre ++ List.replicate (ws.length - pre.length - suf.length) c ++ suf) ws
        have hz := zipP_row_split pre suf c (ws.take (ws.length - suf.length))
          (ws.drop (ws.length - suf.length)) hdl (by omega)
        rw [hAB] at hz
        exact hz

/-! ### The read side's mirror of the same five, and the row equation they give.

    The value side states these in `ExactV`; `alignPL_eq_rowOfG` above is stated here because
    `rowOfG` is. The read-side twins follow it rather than their value-side siblings, so the
    two row equations sit together. -/

/-- A suffix row of the wrong length refuses. -/
theorem zipPA_false_of_length_ne (Ps : List AP) (as : List Attr) (h : Ps.length ≠ as.length) :
    zipPA Ps as = false := by
  cases hz : zipPA Ps as with
  | false => rfl
  | true => exact absurd (zipPA_length Ps as hz) h

/-- A row shorter than the declared prefix refuses. -/
theorem alignPA_short : ∀ (pre : List AP) (sp : Option AP) (as : List Attr),
    as.length < pre.length → alignPA pre sp as = false
  | [], _, _, h => by simp at h
  | _ :: _, sp, [], _ => by cases sp <;> rfl
  | _ :: Ps, sp, _ :: as, h => by
      simp only [alignPA, alignPA_short Ps sp as (by simpa using h), Bool.and_false]

/-- With no spread, the prefix row is the suffix row. -/
theorem alignPA_none_eq_zipPA : ∀ (pre : List AP) (as : List Attr),
    alignPA pre none as = zipPA pre as
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | _ :: Ps, _ :: as => by simp only [alignPA, zipPA, alignPA_none_eq_zipPA Ps as]

/-- …and with a spread it is the prefix padded out to the length. -/
theorem alignPA_some_eq_zipPA : ∀ (pre : List AP) (c : AP) (as : List Attr),
    pre.length ≤ as.length →
    alignPA pre (some c) as = zipPA (pre ++ List.replicate (as.length - pre.length) c) as
  | [], _, [], _ => rfl
  | [], c, _ :: as, _ => by
      have ih := alignPA_some_eq_zipPA [] c as (Nat.zero_le _)
      simp only [List.length_nil, Nat.sub_zero, List.nil_append] at ih ⊢
      simp only [alignPA, List.length_cons, List.replicate_succ, zipPA, ih]
  | _ :: _, _, [], h => by simp at h
  | _ :: Ps, c, _ :: as, h => by
      have ih := alignPA_some_eq_zipPA Ps c as (by simpa using h)
      simp only [alignPA, List.cons_append, zipPA, List.length_cons,
        Nat.succ_sub_succ_eq_sub, ih]

/-- The suffix row splits where the rows do. -/
theorem zipPA_append : ∀ (a₁ b₁ : List AP) (a₂ b₂ : List Attr), a₁.length = a₂.length →
    zipPA (a₁ ++ b₁) (a₂ ++ b₂) = (zipPA a₁ a₂ && zipPA b₁ b₂)
  | [], _, [], _, _ => by simp [zipPA]
  | P :: Ps, b₁, a :: as, b₂, h => by
      simp only [List.cons_append, zipPA, zipPA_append Ps b₁ as b₂ (by simpa using h)]
      exact (Bool.and_assoc _ _ _).symm

/-- The spread row, split at the suffix, on the read side. -/
theorem zipPA_row_split (pre suf : List AP) (c : AP) (A B : List Attr)
    (hB : B.length = suf.length) (hA : pre.length ≤ A.length) :
    (zipPA (pre ++ List.replicate (A.length - pre.length) c) A && zipPA suf B)
      = zipPA (pre ++ List.replicate ((A ++ B).length - pre.length - suf.length) c ++ suf)
          (A ++ B) := by
  have hcount : (A ++ B).length - pre.length - suf.length = A.length - pre.length := by
    simp only [List.length_append, hB]; omega
  rw [hcount, zipPA_append _ _ _ _
      (by simp only [List.length_append, List.length_replicate]; omega)]

/-- **`alignPAL` is its row, applied position for position.** The read-side twin of
    `alignPL_eq_rowOfG`, and the same statement: what a `list` reads at an attribute list of
    length `n` is the row `rowOfG` assigns to `n`, read position by position. -/
theorem alignPAL_eq_rowOfG (pre : List AP) (sp : Option AP) (suf : List AP) (as : List Attr) :
    alignPAL pre sp suf as
      = match rowOfG pre sp suf as.length with
        | none => false
        | some row => zipPA row as := by
  have htl : (as.take (as.length - suf.length)).length = as.length - suf.length := by
    simp only [List.length_take]; omega
  unfold alignPAL
  rcases Nat.lt_or_ge as.length (pre.length + suf.length) with hlt | hge
  · have hrow : rowOfG pre sp suf as.length = none := by
      cases sp with
      | none => simp only [rowOfG]; rw [if_neg (by omega)]
      | some c => simp only [rowOfG]; rw [if_pos (by omega)]
    rw [hrow]
    rcases Nat.lt_or_ge as.length suf.length with hs | hs
    · rw [zipPA_false_of_length_ne _ _ (by simp only [List.length_drop]; omega), Bool.and_false]
    · rw [alignPA_short _ _ _ (by omega), Bool.false_and]
  · have hdl : (as.drop (as.length - suf.length)).length = suf.length := by
      simp only [List.length_drop]; omega
    have hAB : as.take (as.length - suf.length) ++ as.drop (as.length - suf.length) = as :=
      List.take_append_drop _ _
    cases sp with
    | none =>
        rw [alignPA_none_eq_zipPA]
        simp only [rowOfG]
        rcases Nat.eq_or_lt_of_le hge with heq | hlt2
        · rw [if_pos heq.symm]
          show _ = zipPA (pre ++ suf) as
          have hz := (zipPA_append pre suf (as.take (as.length - suf.length))
            (as.drop (as.length - suf.length)) (by omega)).symm
          rw [hAB] at hz
          exact hz
        · rw [if_neg (by omega)]
          show _ = false
          rw [zipPA_false_of_length_ne _ _ (by omega), Bool.false_and]
    | some c =>
        rw [alignPA_some_eq_zipPA _ _ _ (by omega)]
        simp only [rowOfG]
        rw [if_neg (by omega)]
        show _ = zipPA (pre ++ List.replicate (as.length - pre.length - suf.length) c ++ suf) as
        have hz := zipPA_row_split pre suf c (as.take (as.length - suf.length))
          (as.drop (as.length - suf.length)) hdl (by omega)
        rw [hAB] at hz
        exact hz

/-- A row the shape accepts has exactly the length asked of it. -/
theorem rowOfG_length {α : Type} {pre : List α} {sp : Option α} {suf : List α} {n row}
    (h : rowOfG pre sp suf n = some row) : row.length = n := by
  cases sp with
  | none =>
      simp only [rowOfG] at h
      split at h
      · next he =>
          simp only [Option.some.injEq] at h
          subst h
          simp only [List.length_append]
          omega
      · exact absurd h (by simp)
  | some c =>
      simp only [rowOfG] at h
      split at h
      · exact absurd h (by simp)
      · next he =>
          simp only [Option.some.injEq] at h
          subst h
          simp only [List.length_append, List.length_replicate]
          omega

/-- The row of a shape with no spread, as an `if`: the shape has a row at its own arity and
    at no other length. -/
theorem rowOfG_none_eq {α : Type} (pre suf : List α) (n : Nat) :
    rowOfG pre none suf n
      = if n = pre.length + suf.length then some (pre ++ suf) else none := rfl

/-- …and of a spreading shape, which has a row at every length from its arity up. -/
theorem rowOfG_some_eq {α : Type} (pre : List α) (c : α) (suf : List α) (n : Nat) :
    rowOfG pre (some c) suf n
      = if n < pre.length + suf.length then none
        else some (pre ++ List.replicate (n - pre.length - suf.length) c ++ suf) := rfl

/-- Every term a row holds comes from the shape: a declared position, or the spread. -/
theorem rowOfG_mem {α : Type} {pre : List α} {sp : Option α} {suf : List α} {n row}
    (h : rowOfG pre sp suf n = some row) {a : α} (ha : a ∈ row) :
    a ∈ pre ∨ a ∈ sp ∨ a ∈ suf := by
  cases sp with
  | none =>
      rw [rowOfG_none_eq] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        rcases List.mem_append.mp ha with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inr h')
      · exact absurd h (by simp)
  | some c =>
      rw [rowOfG_some_eq] at h
      split at h
      · exact absurd h (by simp)
      · simp only [Option.some.injEq] at h
        subst h
        rcases List.mem_append.mp ha with h' | h'
        · rcases List.mem_append.mp h' with h'' | h''
          · exact Or.inl h''
          · exact Or.inr (Or.inl (by rw [List.eq_of_mem_replicate h'']; rfl))
        · exact Or.inr (Or.inr h')

/-- Two rows over the same three parts, related position for position. -/
theorem forall₂_replicate {α β : Type} {R : α → β → Prop} {a : α} {b : β} (hab : R a b) :
    ∀ n, List.Forall₂ R (List.replicate n a) (List.replicate n b)
  | 0 => .nil
  | n + 1 => by
      simp only [List.replicate_succ]
      exact .cons hab (forall₂_replicate hab n)

/-- …and two such pairs, appended: a row built in parts carries the relation in parts. -/
theorem forall₂_append {α β : Type} {R : α → β → Prop} {a₁ a₂ : List α} {b₁ b₂ : List β} :
    List.Forall₂ R a₁ b₁ → List.Forall₂ R a₂ b₂ →
      List.Forall₂ R (a₁ ++ a₂) (b₁ ++ b₂) := by
  intro h₁ h₂
  induction h₁ with
  | nil => exact h₂
  | cons hh _ ih => exact .cons hh ih

/-- **The three-place row relation**, carried as a `Forall₂` over the pair list, as
    `zipF_lift` and `alignP_meet_zip` already carry it. The four lemmas below close it under
    the four ways the meet cuts and rebuilds a row. -/
theorem forall₂_zip_append {α β γ : Type} {R : α × β → γ → Prop}
    {a₁ a₂ : List α} {b₁ b₂ : List β} {c₁ c₂ : List γ}
    (hl : a₁.length = b₁.length)
    (h₁ : List.Forall₂ R (a₁.zip b₁) c₁) (h₂ : List.Forall₂ R (a₂.zip b₂) c₂) :
    List.Forall₂ R ((a₁ ++ a₂).zip (b₁ ++ b₂)) (c₁ ++ c₂) := by
  rw [List.zip_append hl]
  exact forall₂_append h₁ h₂

/-- …the spread, held at as many positions as the length needs. -/
theorem forall₂_zip_replicate {α β γ : Type} {R : α × β → γ → Prop} {a : α} {b : β} {c : γ}
    (h : R (a, b) c) (n : Nat) :
    List.Forall₂ R ((List.replicate n a).zip (List.replicate n b)) (List.replicate n c) := by
  rw [List.zip_replicate, Nat.min_self]
  exact forall₂_replicate h n

/-- …the prefix the answer keeps. -/
theorem forall₂_zip_take {α β γ : Type} {R : α × β → γ → Prop} :
    ∀ {as : List α} {bs : List β} {cs : List γ} (n : Nat),
      List.Forall₂ R (as.zip bs) cs →
      List.Forall₂ R ((as.take n).zip (bs.take n)) (cs.take n) := by
  intro as bs cs n
  induction n generalizing as bs cs with
  | zero => intro _; simp
  | succ n ih =>
      intro h
      cases as with
      | nil => cases h; simp
      | cons a as' =>
          cases bs with
          | nil => cases h; simp
          | cons b bs' =>
              rw [List.zip_cons_cons] at h
              cases h with
              | cons hh ht => simpa using List.Forall₂.cons hh (ih ht)

/-- …and the suffix the answer keeps. -/
theorem forall₂_zip_drop {α β γ : Type} {R : α × β → γ → Prop} :
    ∀ {as : List α} {bs : List β} {cs : List γ} (n : Nat),
      List.Forall₂ R (as.zip bs) cs →
      List.Forall₂ R ((as.drop n).zip (bs.drop n)) (cs.drop n) := by
  intro as bs cs n
  induction n generalizing as bs cs with
  | zero => intro h; simpa using h
  | succ n ih =>
      intro h
      cases as with
      | nil => cases h; simp
      | cons a as' =>
          cases bs with
          | nil => cases h; simp
          | cons b bs' =>
              rw [List.zip_cons_cons] at h
              cases h with
              | cons _ ht => simpa using ih ht

/-- **A row of rows is the mapped row.** The value side, the read side and the derivation
    each hold their shape as terms and read it through one map, so every row equation is
    stated over terms once. -/
theorem rowOfG_map {α β : Type} (g : α → β) (pre : List α) (sp : Option α) (suf : List α)
    (n : Nat) :
    rowOfG (pre.map g) (sp.map g) (suf.map g) n
      = (rowOfG pre sp suf n).map (List.map g) := by
  cases sp with
  | none =>
      simp only [rowOfG, Option.map_none, List.length_map]
      split <;> simp [List.map_append]
  | some c =>
      simp only [rowOfG, Option.map_some, List.length_map]
      split <;> simp [List.map_append, List.map_replicate]

/-- **The row transfers a relation.** Two shapes whose prefixes, spreads and suffixes are
    related position for position assign related rows at every length. This is the one
    lemma the meet's three semantic families share: each reads its own relation off the
    two rows rather than off the shapes. -/
theorem rowOfG_forall₂ {α β : Type} {R : α → β → Prop}
    {pre₁ : List α} {pre₂ : List β} {sp₁ : Option α} {sp₂ : Option β}
    {suf₁ : List α} {suf₂ : List β}
    (hp : List.Forall₂ R pre₁ pre₂)
    (hs : (sp₁ = none ∧ sp₂ = none) ∨ ∃ a b, sp₁ = some a ∧ sp₂ = some b ∧ R a b)
    (hf : List.Forall₂ R suf₁ suf₂) {n : Nat} {r₁ : List α} {r₂ : List β}
    (h₁ : rowOfG pre₁ sp₁ suf₁ n = some r₁) (h₂ : rowOfG pre₂ sp₂ suf₂ n = some r₂) :
    List.Forall₂ R r₁ r₂ := by
  have hlp := hp.length_eq
  have hlf := hf.length_eq
  rcases hs with ⟨rfl, rfl⟩ | ⟨a, b, rfl, rfl, hab⟩
  · simp only [rowOfG] at h₁ h₂
    split at h₁
    · next he₁ =>
        split at h₂
        · next he₂ =>
            simp only [Option.some.injEq] at h₁ h₂
            subst h₁; subst h₂
            exact forall₂_append hp hf
        · exact absurd h₂ (by simp)
    · exact absurd h₁ (by simp)
  · simp only [rowOfG] at h₁ h₂
    split at h₁
    · exact absurd h₁ (by simp)
    · next he₁ =>
        split at h₂
        · exact absurd h₂ (by simp)
        · next he₂ =>
            simp only [Option.some.injEq] at h₁ h₂
            subst h₁; subst h₂
            refine forall₂_append (forall₂_append hp ?_) hf
            have hc : n - pre₁.length - suf₁.length = n - pre₂.length - suf₂.length := by omega
            rw [hc]
            exact forall₂_replicate hab _

/-- …and the row of a shape whose parts match another's lengths exists wherever that one's
    does, related to it. This is the form the meet uses: it holds the FUNCTION row and needs
    the TERM row that stands behind it. -/
theorem rowOfG_forall₂_left {α β : Type} {R : α → β → Prop}
    {pre₁ : List α} {pre₂ : List β} {sp₁ : Option α} {sp₂ : Option β}
    {suf₁ : List α} {suf₂ : List β}
    (hp : List.Forall₂ R pre₁ pre₂)
    (hs : (sp₁ = none ∧ sp₂ = none) ∨ ∃ a b, sp₁ = some a ∧ sp₂ = some b ∧ R a b)
    (hf : List.Forall₂ R suf₁ suf₂) {n : Nat} {r₂ : List β}
    (h₂ : rowOfG pre₂ sp₂ suf₂ n = some r₂) :
    ∃ r₁, rowOfG pre₁ sp₁ suf₁ n = some r₁ ∧ List.Forall₂ R r₁ r₂ := by
  have hlp := hp.length_eq
  have hlf := hf.length_eq
  have hex : ∃ r₁, rowOfG pre₁ sp₁ suf₁ n = some r₁ := by
    rcases hs with ⟨rfl, rfl⟩ | ⟨a, b, rfl, rfl, _⟩
    · simp only [rowOfG] at h₂ ⊢
      split at h₂
      · next he => exact ⟨_, if_pos (by omega)⟩
      · exact absurd h₂ (by simp)
    · simp only [rowOfG] at h₂ ⊢
      split at h₂
      · exact absurd h₂ (by simp)
      · next he => exact ⟨_, if_neg (by omega)⟩
  obtain ⟨r₁, h₁⟩ := hex
  exact ⟨r₁, h₁, rowOfG_forall₂ hp hs hf h₁ h₂⟩

/-- …and a spreading shape has a row exactly from its arity up. -/
theorem rowOfG_some_isSome {α : Type} (pre : List α) (c : α) (suf : List α) (n : Nat) :
    (rowOfG pre (some c) suf n).isSome = decide (pre.length + suf.length ≤ n) := by
  rw [rowOfG_some_eq]
  split <;> simp_all

/-- A spreading shape has a row at every length its prefix and suffix fit inside. -/
theorem rowOfG_total {α : Type} {pre suf : List α} {c : α} {n : Nat}
    (hn : pre.length + suf.length ≤ n) :
    ∃ row, rowOfG pre (some c) suf n = some row := by
  simp only [rowOfG]
  exact ⟨_, if_neg (by omega)⟩

/-- **A spreading shape's row at any length is its row at one length, re-spread.** Cut the
    shorter row at `P`, insert the spread as often as the longer length needs, and the
    longer row comes back. This is what the `list` meet owes and what the row relations
    alone cannot give: the meet builds its answer from the two rows at ONE length, and the
    admission obligation is at EVERY length. `P` and `S` are the answer's prefix and suffix
    lengths, which each operand's own prefix and suffix fit inside. -/
theorem rowOfG_respread {α : Type} {pre suf : List α} {c : α} {P S n : Nat}
    (hP : pre.length ≤ P) (hS : suf.length ≤ S) (hn : P + S ≤ n)
    {rN rn : List α}
    (hN : rowOfG pre (some c) suf (P + S) = some rN)
    (hm : rowOfG pre (some c) suf n = some rn) :
    rn = rN.take P ++ List.replicate (n - P - S) c ++ rN.drop P := by
  simp only [rowOfG] at hN hm
  rw [if_neg (by omega)] at hN
  rw [if_neg (by omega)] at hm
  simp only [Option.some.injEq] at hN hm
  subst hN; subst hm
  have h1 : ((pre ++ List.replicate (P + S - pre.length - suf.length) c) ++ suf).take P
      = pre ++ List.replicate (P - pre.length) c := by
    simp only [List.take_append, List.length_append, List.length_replicate,
      List.take_replicate, List.take_of_length_le hP]
    rw [show min (P - pre.length) (P + S - pre.length - suf.length) = P - pre.length by omega,
      show P - (pre.length + (P + S - pre.length - suf.length)) = 0 by omega]
    simp
  have h2 : ((pre ++ List.replicate (P + S - pre.length - suf.length) c) ++ suf).drop P
      = List.replicate (S - suf.length) c ++ suf := by
    simp only [List.drop_append, List.length_append, List.length_replicate,
      List.drop_replicate, List.drop_eq_nil_of_le hP]
    rw [show P - (pre.length + (P + S - pre.length - suf.length)) = 0 by omega,
      show P + S - pre.length - suf.length - (P - pre.length) = S - suf.length by omega]
    simp
  rw [h1, h2, show n - pre.length - suf.length
      = (P - pre.length) + ((n - P - S) + (S - suf.length)) by omega,
    List.replicate_add, List.replicate_add]
  simp only [List.append_assoc]

/-- **One side dominates the other**, in the prefix and in the suffix at once.

    This is the whole of the `list` meet's refusal, and it is a fact about lengths alone.
    With both shapes spreading, the meet admits a value of length `n` exactly when
    `n ≥ max (p₁+s₁) (p₂+s₂)`, while the widest `list` the answer can spell admits
    `n ≥ max p₁ p₂ + max s₁ s₂`. The second is never smaller, and the two are EQUAL exactly
    when one side's prefix and suffix are both at least the other's. Elsewhere a window of
    lengths sits in the intersection that no single `list` states, because a `list` carries
    one prefix and one suffix and the window needs two shapes. There the meet refuses. -/
def dominates (p₁ s₁ p₂ s₂ : Nat) : Bool :=
  (decide (p₂ ≤ p₁) && decide (s₂ ≤ s₁)) || (decide (p₁ ≤ p₂) && decide (s₁ ≤ s₂))

/-- **Dominance is exactly the equation the answer needs.** The widest `list` the answer can
    spell starts at `max p₁ p₂ + max s₁ s₂`, and the intersection starts at
    `max (p₁+s₁) (p₂+s₂)`. Where one side dominates, the two agree, so the answer refuses a
    length exactly where a factor does. -/
theorem dominates_max {p₁ s₁ p₂ s₂ : Nat} (h : dominates p₁ s₁ p₂ s₂ = true) :
    max p₁ p₂ + max s₁ s₂ = max (p₁ + s₁) (p₂ + s₂) := by
  simp only [dominates, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  omega

/-- Two `list` shapes met, the left as partially applied meets and the right as terms.

    Three branches, and only the first can refuse. **Both spreading**: the answer is the
    row at `max p₁ p₂ + max s₁ s₂`, split back into that prefix and that suffix, with the
    spreads met; `dominates` says when that is the exact intersection, and the meet refuses
    otherwise. **Either side without a spread**: that side's arity is fixed, so the answer
    FLATTENS to one prefix of exactly that length with no spread and no suffix; a length the
    other side cannot reach is the empty intersection, which is `.never`. Flattening rather
    than keeping the longer prefix and the longer suffix is what the fixed-arity case needs:
    the two overhangs can collide, and at a fixed arity there is no spread to meet them
    against. -/
def listMeetRow (fpre : List (Term → Option Term)) (fsp : Option (Term → Option Term))
    (fsuf : List (Term → Option Term)) (pre₂ : List Term) (sp₂ : Option Term)
    (suf₂ : List Term) : Option Term :=
  match fsp, sp₂ with
  | some f, some c =>
      if dominates fpre.length fsuf.length pre₂.length suf₂.length then
        match f c,
            rowOfG fpre (some f) fsuf
              (max fpre.length pre₂.length + max fsuf.length suf₂.length),
            rowOfG pre₂ (some c) suf₂
              (max fpre.length pre₂.length + max fsuf.length suf₂.length) with
        | some sp, some fs, some us =>
            (allSome (zipF fs us)).map fun row =>
              Term.listOf (row.take (max fpre.length pre₂.length)) (some sp)
                (row.drop (max fpre.length pre₂.length))
        | none, _, _ => none
        | _, _, _ => some .never
      else none
  | none, _ =>
      match rowOfG fpre none fsuf (fpre.length + fsuf.length),
          rowOfG pre₂ sp₂ suf₂ (fpre.length + fsuf.length) with
      | some fs, some us => (allSome (zipF fs us)).map fun row => Term.listOf row none []
      | _, _ => some .never
  | some f, none =>
      match rowOfG fpre (some f) fsuf (pre₂.length + suf₂.length),
          rowOfG pre₂ none suf₂ (pre₂.length + suf₂.length) with
      | some fs, some us => (allSome (zipF fs us)).map fun row => Term.listOf row none []
      | _, _ => some .never

/-- The family of the one positional container: the one shape a positional value can meet,
    and the bottom at every constructor in another value slot. `opaq` refuses, because its
    closed form states no positional shape to intersect. -/
def famList (fpre : List (Term → Option Term)) (fsp : Option (Term → Option Term))
    (fsuf : List (Term → Option Term)) : Term → Option Term
  | .list pre₂ sp₂ suf₂ => listMeetRow fpre fsp fsuf pre₂ sp₂ suf₂
  | .opaq => none
  | _ => some .never


/-- Every answer of `listMeetRow` is the bottom or a list: each branch ends in `Term.listOf`,
    and a normalised list is one or the other. -/
theorem listMeetRow_isList {fpre : List (Term → Option Term)}
    {fsp : Option (Term → Option Term)} {fsuf : List (Term → Option Term)}
    {pre₂ : List Term} {sp₂ : Option Term} {suf₂ : List Term} {z : Term}
    (h : listMeetRow fpre fsp fsuf pre₂ sp₂ suf₂ = some z) :
    z = .never ∨ ∃ p q s, z = .list p q s := by
  have hA : ∀ (o : Option (List Term)) (g : List Term → Term),
      (∀ row, g row = .never ∨ ∃ p q s, g row = .list p q s) →
      o.map g = some z → z = .never ∨ ∃ p q s, z = .list p q s := by
    intro o g hg ho
    obtain ⟨row, _, rfl⟩ := Option.map_eq_some_iff.mp ho
    exact hg row
  have hTake : ∀ (P : Nat) (q : Option Term) (row : List Term),
      Term.listOf (row.take P) q (row.drop P) = .never ∨
        ∃ p q' s, Term.listOf (row.take P) q (row.drop P) = .list p q' s :=
    fun P q row => (listOf_cases _ _ _).imp id fun hc => ⟨_, _, _, hc⟩
  have hFlat : ∀ row : List Term, Term.listOf row none [] = .never ∨
      ∃ p q' s, Term.listOf row none [] = .list p q' s :=
    fun row => (listOf_cases _ _ _).imp id fun hc => ⟨_, _, _, hc⟩
  unfold listMeetRow at h
  split at h
  · split at h
    · split at h
      · exact hA _ _ (hTake _ _) h
      · exact absurd h (by simp)
      · simp only [Option.some.injEq] at h; exact Or.inl h.symm
    · exact absurd h (by simp)
  · split at h
    · exact hA _ _ hFlat h
    · simp only [Option.some.injEq] at h; exact Or.inl h.symm
  · split at h
    · exact hA _ _ hFlat h
    · simp only [Option.some.injEq] at h; exact Or.inl h.symm

/-- …so every answer of the family is the bottom or a list. -/
theorem famList_isList {fpre : List (Term → Option Term)}
    {fsp : Option (Term → Option Term)} {fsuf : List (Term → Option Term)} {y z : Term}
    (h : famList fpre fsp fsuf y = some z) :
    z = .never ∨ ∃ p q s, z = .list p q s := by
  cases y <;>
    first
      | exact listMeetRow_isList h
      | (simp only [famList, Option.some.injEq] at h; exact Or.inl h.symm)
      | exact absurd h (by simp [famList])

/-- **The term an undeclared name holds**: the open block's, and `never` where the body is
    closed. `Adm_closed_eq_never_block` is why the two spellings of a closed body are one body. -/
def Body.block (b : Body) : Term :=
  match b.wild with
  | none => .never
  | some t => t

/-- A closed traversal and a traversal through a block that admits nothing agree. -/
theorem objAdmV_none_never (fs : MapOf VP) (keys : Finset Name) (g : {k // k ∈ keys} → Value) :
    objAdmV fs none keys g = objAdmV fs (some (fun _ => false)) keys g := by
  unfold objAdmV
  exact decide_eq_decide.mpr (forall_congr' fun k => by unfold entryP; cases fs.at k.1 <;> exact Iff.rfl)

/-- …and the same on the read side. -/
theorem objAdmA_none_never (fs : MapOf AP) (keys : Finset Name) (g : {k // k ∈ keys} → Attr) :
    objAdmA fs none keys g = objAdmA fs (some (fun _ => false)) keys g := by
  unfold objAdmA
  exact decide_eq_decide.mpr (forall_congr' fun k => by unfold entryPA; cases fs.at k.1 <;> exact Iff.rfl)

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
      show (reqPresentT D f keys && objAdmA _ none keys g) =
        (reqPresentT D f keys && objAdmA _ (some (fun _ => false)) keys g)
      rw [objAdmA_none_never]
  | _ => rfl

/-- A slot met through one term's meet, keeping the slot's mark. It is `ObjectSlot.meet
    (.optional t)` with `Term.meet t` passed applied, which keeps the recursion structural. -/
def ObjectSlot.through (m : Term → Option Term) : ObjectSlot → Option ObjectSlot
  | .req y => (m y).map .req
  | .optional y => (m y).map .optional

/-- **The meet at one name of either body.** A body is a total function from the key space to
    a slot, presented as the declared slots and a default: an undeclared name holds `optional`
    of the block. So a name the left body declares meets the right body's slot at that name,
    and a name only the right body declares meets the left body's block. -/
def objSlot (a b : Body) (g : {k // k ∈ a.fields} → ObjectSlot → Option ObjectSlot)
    (mw : Term → Option Term) (k : {k // k ∈ a.fields ∪ b.fields}) : Option ObjectSlot :=
  if h : k.1 ∈ a.fields then
    g ⟨k.1, h⟩ (if h' : k.1 ∈ b.fields then b.at ⟨k.1, h'⟩ else .optional b.block)
  else
    ObjectSlot.through mw (b.at ⟨k.1, (Finset.mem_union.mp k.2).resolve_left h⟩)

/-- A met slot that says the name is absent: `optional never`. -/
def ObjectSlot.isAbsentOpt : Option ObjectSlot → Bool
  | some (.optional t) => t.isNever
  | _ => false

/-- **Two objects, met pointwise.** Every name of either body meets at its two slots, and the
    blocks meet as the default. A product is the bottom when any factor is, so a slot at the
    bottom decides before a slot that refuses.

    **The normal form drops a name that states the default**, where the default is `never`: in a
    closed body `optional never` is what an undeclared name already holds. An open default has
    no decidable equality to test, so there every name is kept as written. -/
def objObj (a : Body) (g : {k // k ∈ a.fields} → ObjectSlot → Option ObjectSlot)
    (mw : Term → Option Term) (b : Body) : Option Term :=
  if decide (∃ k : {k // k ∈ a.fields ∪ b.fields},
      ((objSlot a b g mw k).map ObjectSlot.isBottom) = some true) then some .never
  else
    match mw b.block with
    | none => none
    | some zb =>
      if decide (∀ k : {k // k ∈ a.fields ∪ b.fields}, (objSlot a b g mw k).isSome = true) then
        let keep : Name → Bool := fun k =>
          if h : k ∈ a.fields ∪ b.fields then
            !(zb.isNever && ObjectSlot.isAbsentOpt (objSlot a b g mw ⟨k, h⟩))
          else false
        some (.object (.mk ((a.fields ∪ b.fields).filter (fun k => keep k = true))
          (fun k => (objSlot a b g mw ⟨k.1, (Finset.mem_filter.mp k.2).1⟩).getD
            (.optional .never))
          (if zb.isNever then none else some zb)))
      else none

def famObj (a : Body) (g : {k // k ∈ a.fields} → ObjectSlot → Option ObjectSlot)
    (mw : Term → Option Term) : Term → Option Term
  | .object b => objObj a g mw b
  | .opaq => none
  | _ => some .never

mutual
/-- **The intersection of two admissions, as a term**, by structural recursion on the left
    operand. Every row keeps the left operand on the left. -/
def Term.meet : Term → Term → Option Term
  | .never, _ => some .never
  | .lazy x, y => Term.meet x y
  | .held _ _ _ _, .never => some .never
  | .held _ _ _ _, _ => none
  | .refine _ _, .never => some .never
  | .refine x p, y => if p.isData then (Term.meet x y).map (fun z => Term.refineOf z p) else none
  | .union _, .never => some .never
  | .union os, y => (allSome (Term.meetSL os y)).bind
      (fun zs => some (Term.ofOptions (zs.filter (fun z => !z.isNever))))
  | .string, y => meetSRight famString y
  | .number, y => meetSRight famNumber y
  | .boolean, y => meetSRight famBoolean y
  | .binary, y => meetSRight famBinary y
  | .null, y => meetSRight famNull y
  | .literal k v, y => meetSRight (famLit k v) y
  | .set b, y => meetSRight (famSet b) y
  | .opaq, y => meetSRight (famOpaq) y
  | .list pre sp suf, y =>
      meetSRight (famList (Term.meetSTs pre)
        (match sp with | none => none | some t => some (Term.meet t))
        (Term.meetSTs suf)) y
  | .object (.mk fs f w), y =>
      meetSRight (famObj (.mk fs f w) (fun k => ObjectSlot.meet (f k))
        (match w with | none => fun _ => some .never | some t => Term.meet t)) y
termination_by structural x _ => x
def Term.meetSL : List Term → Term → List (Option Term)
  | [], _ => [] | x :: xs, y => Term.meet x y :: Term.meetSL xs y
termination_by structural xs _ => xs
def Term.meetSTs : List Term → List (Term → Option Term)
  | [] => [] | t :: ts => Term.meet t :: Term.meetSTs ts
termination_by structural ts => ts
/-- The complete two-mark slot meet. Required presence dominates optional presence. -/
def ObjectSlot.meet : ObjectSlot → ObjectSlot → Option ObjectSlot
  | .req x, .req y => (Term.meet x y).map .req
  | .req x, .optional y => (Term.meet x y).map .req
  | .optional x, .req y => (Term.meet x y).map .req
  | .optional x, .optional y => (Term.meet x y).map .optional
termination_by structural f _ => f
end

/-! ## The union certificate

The certificate is defined here, after the meet, because one of its two tests is the meet. -/

/-- **Whether two terms meet at the bottom.** A pair that the meet cannot state answers `false`,
    so the pair is not certified. -/
def meetNever (x y : Term) : Bool := (Term.meet x y).any Term.isNever

mutual
/-- Whether a `held` occurs in the term. -/
def hasHeld : Term → Bool
  | .held _ _ _ _ => true
  | .refine t _ => hasHeld t
  | .lazy t => hasHeld t
  | .list pre sp suf => hasHeldL pre || hasHeldO sp || hasHeldL suf
  | .object b => hasHeldB b
  | .union os => hasHeldL os
  | .string | .number | .boolean | .binary | .null | .literal _ _ | .set _ | .opaq
  | .never => false
def hasHeldL : List Term → Bool
  | [] => false
  | t :: ts => hasHeld t || hasHeldL ts
def hasHeldO : Option Term → Bool
  | none => false
  | some t => hasHeld t
def hasHeldB : Body → Bool
  | .mk fs f w => decide (∃ k : {k // k ∈ fs}, hasHeldS (f k) = true) || hasHeldO w
def hasHeldS : ObjectSlot → Bool
  | .req t => hasHeld t
  | .optional t => hasHeld t
end

mutual
/-- **Whether a `held` occurs below a `union`.** The views keep a `union` as written, and the
    view of a `union` with a `held` below it would need the join of the views of its options.
    The model has that join only as a certified union, so `certViews` refuses such a term. -/
def heldBelowUnion : Term → Bool
  | .held t P _ _ => heldBelowUnion t || heldBelowUnion P
  | .refine t _ => heldBelowUnion t
  | .lazy t => heldBelowUnion t
  | .list pre sp suf => heldBelowUnionL pre || heldBelowUnionO sp || heldBelowUnionL suf
  | .object b => heldBelowUnionB b
  | .union os => hasHeldL os
  | .string | .number | .boolean | .binary | .null | .literal _ _ | .set _ | .opaq
  | .never => false
def heldBelowUnionL : List Term → Bool
  | [] => false
  | t :: ts => heldBelowUnion t || heldBelowUnionL ts
def heldBelowUnionO : Option Term → Bool
  | none => false
  | some t => heldBelowUnion t
def heldBelowUnionB : Body → Bool
  | .mk fs f w =>
      decide (∃ k : {k // k ∈ fs}, heldBelowUnionS (f k) = true) || heldBelowUnionO w
def heldBelowUnionS : ObjectSlot → Bool
  | .req t => heldBelowUnion t
  | .optional t => heldBelowUnion t
end

mutual
/-- **The caller-side view**: each `held` becomes its caller-side term. The view admits each
    value that the term admits, below every `union` that holds no `held`. -/
def writeView : Term → Term
  | .held _ P _ _ => writeView P
  | .refine t p => .refine (writeView t) p
  | .lazy t => .lazy (writeView t)
  | .list pre sp suf => .list (writeViewL pre) (writeViewO sp) (writeViewL suf)
  | .object b => .object (writeViewB b)
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
  | .lazy t => .lazy (readView t)
  | .list pre sp suf => .list (readViewL pre) (readViewO sp) (readViewL suf)
  | .object b => .object (readViewB b)
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
    `Orth` and the meet see neither: occupancy sees only kinds, and the meet refuses a `held`.
    The caller-side views answer the write question and the stored-side views answer the read
    question. Each view is held-free, so the two tests are `Orth` and the meet. The test runs
    only where a `held` occurs, and a `held` below a `union` is refused. -/
def certViews (x y : Term) : Bool :=
  (hasHeld x || hasHeld y) && !heldBelowUnion x && !heldBelowUnion y
    && (Orth (writeView x) (writeView y) || meetNever (writeView x) (writeView y))
    && (Orth (readView x) (readView y) || meetNever (readView x) (readView y))

/-- **The certificate for one pair of options.** The meet certifies two arrays told apart by a
    literal position, and the empty list beside a list that holds one element or more, which
    `Orth` misses. The meet meets two `each` predicates, so two string sets whose members are
    disjoint meet at the bottom, and `Orth` certifies that pair too. No theorem states that the
    meet certifies every pair that `Orth` certifies, so `Orth` stays a disjunct. A `held` reaches
    `Orth` only through its occupancies and the meet not at all, so `certViews` is the third
    disjunct. -/
def certPair (x y : Term) : Bool := Orth x y || meetNever x y || certViews x y

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
example : ObjectSlot.meet (.optional .string) (.req .string) = some (.req .string) := by rfl

/-- Required slots meet without comparing values outside their carried terms. -/
example : ObjectSlot.meet (.req .string) (.req .string) = some (.req .string) := by rfl

/-! ## What the rows answer

Worked pairs, one per class, checked by the equation compiler rather than described. The first is
the example the meet exists for: an array admits every length and a tuple pins one, so the meet is
the tuple. -/

example : Term.meet (.array .string) (.tuple [.literal .string "a"] none)
    = some (.tuple [.literal .string "a"] none) := by rfl

/-- Two value kinds that never meet. -/
example : Term.meet .string .number = some .never := by rfl

/-- A literal against its own base is the literal: the finer of the two. -/
example : Term.meet (.literal .string "a") .string = some (.literal .string "a") := by rfl

/-- …and against another value of the same base, nothing. -/
example : Term.meet (.literal .string "a") (.literal .string "b") = some .never := by rfl

/-- A literal at a base that shares nothing with the partner is still the bottom. -/
example : Term.meet (.literal .string "1") .boolean = some .never := by rfl

/-- **The null point needs no row of its own.** A null point is the null term joined by a union,
    so the union rows distribute over it and the ground rows answer each cell. This is the pair
    that had a row and got it wrong: the wrapper this replaced dropped the point at every
    partner but another wrapper and a `null`, and `opaq` holds the point. -/
example : Term.meet (.union [.string, .null]) .opaq = some (.union [.string, .null]) := by rfl

/-- …and against the null term alone the string cell is the bottom, so one option survives. -/
example : Term.meet (.union [.string, .null]) .null = some .null := by rfl

/-- **Two open factors meet pointwise.** The left body requires `x` and the right does not
    declare it, so `x` meets the right body's open block and stays required. `y` meets the left
    body's block and stays optional, and the blocks meet to `string`. The two examples below are
    a value both admit, which the meet admits too. -/
example :
    (Term.meet
        (.object (.mk {"x"} (fun _ => .req .string) (some .string)))
        (.object (.mk {"y"} (fun _ => .optional .string) (some .string)))).map
      (fun z => match z with
        | .object b => (decide ("x" ∈ b.fields), decide ("y" ∈ b.fields), b.wild.isSome)
        | _ => (false, false, false))
      = some (true, true, true) := by rfl

/-- The left body admits `{x := "1"}` through its declared slot… -/
example : Adm (.object (.mk {"x"} (fun _ => .req .string) (some .string)))
    (.map {"x"} (fun _ => .str "1")) = true := by
  simp [Adm, AdmBody, valPresentT, objAdmV, entryP, MapOf.at, AdmField]

/-- …and the right body admits it through its open block, at a name it does not declare. -/
example : Adm (.object (.mk {"y"} (fun _ => .optional .string) (some .string)))
    (.map {"x"} (fun _ => .str "1")) = true := by
  simp [Adm, AdmBody, valPresentT, objAdmV, entryP, MapOf.at, AdmField, AdmWild]
  apply decide_eq_true
  intro k
  rw [if_neg (by have hk := k.2; simp only [Finset.mem_singleton] at hk; simp [hk])]

/-! ### The presence table

Four two-mark cells. Required presence dominates optional presence, and each cell meets the
carried terms. -/

/-- The four two-mark rows reduce in the kernel. -/
example : ObjectSlot.meet (.req .string) (.optional .string) = some (.req .string) := by rfl
example : ObjectSlot.meet (.optional .string) (.req .string) = some (.req .string) := by rfl
example : ObjectSlot.meet (.optional .string) (.optional .string) = some (.optional .string) := by rfl

/-- A `req` slot over the bottom is still the bottom and not a refusal: both halves force the
    name present, so both agree that nothing satisfies the object. -/
example : ObjectSlot.meet (.req .string) (.req .boolean) = some (.req .never) := by rfl



/-- **Two closed factors with no shared name meet at the closed body with no name.** Each name
    meets the other body's default `never` at `optional never`, which is the default itself, so
    the normal form drops the name. -/
example :
    (Term.meet
        (.object (.mk {"x"} (fun _ => .optional .string) none))
        (.object (.mk {"y"} (fun _ => .optional .string) none))).map
      (fun z => match z with
        | .object b => (decide ("x" ∈ b.fields), decide ("y" ∈ b.fields), b.wild.isSome)
        | _ => (true, true, true))
      = some (false, false, false) := by rfl

/-- **`Orth` misses a pair that the meet certifies.** These two options declare the same name
    with the same mark and no literal, so no phase of `Orth` tells them apart… -/
example : Orth (.object (.mk {"a"} (fun _ => .req .string) none))
    (.object (.mk {"a"} (fun _ => .req .boolean) none)) = false := by
  simp [Orth, Orth1, OrthM, OrthS, OrthL, occV, occOnly, Slot.all,
    namesSeparate, presenceMeetsBot, BodySpec.presenceAt, ObjectSlot.presence,
    ObjectSlot.isReq, Term.isNever, Body.spec, altsOfField,
    specOf, litDisjAt, altsDisj, MapOf.at, Finset.mem_singleton]

/-- …and the meet answers the bottom, because the required slot meets `string` with `boolean`.
    So the union is certified. -/
example : unionOk [.object (.mk {"a"} (fun _ => .req .string) none),
    .object (.mk {"a"} (fun _ => .req .boolean) none)] = true := by decide

/-! ### The bottom bubbles up through a required slot

A slot that must hold a value passes the bottom up; a slot that may be empty stops it. So the
meet's output is normal, and `Term.isNever` is the whole of the union guard's filter again. -/

/-- A tuple's declared position is such a slot… -/
example : Term.meet (.tuple [.string] none) (.tuple [.boolean] none) = some .never := by rfl

/-- …an `array`'s element is not, because an array over the bottom holds the empty list. -/
example : Term.meet (.array .string) (.array .boolean) = some (.array .never) := by rfl

/-- A refinement's inner term is such a slot, and this is the pair that made a union of empty
    options: each option met the partner at a refinement over the bottom, which the filter could
    not see. Both options now answer the bottom and the filter drops them. -/
example : Term.meet
    (.refine .string (.members .string ⟨{"1"}, Finset.singleton_nonempty _⟩)) .null
      = some .never := by rfl

example : unionOk [.object (.mk {"x"} (fun _ => .optional .string) none)] = true := by
  simp [unionOk, certAll]

example : unionOk [.object (.mk {"x"} (fun _ => .req .string) none)]
    = true := by
  simp [unionOk, certAll]

/-- …and an **open** object separates from nothing on the names phase. Its open block makes
    an undeclared name the top, so no name meets at the bottom. `unionOk` admits the open
    object, because the structural lemmas read the block, so a singleton union admits every
    value the option admits. -/
example : unionOk [.object (.mk {"a"} (fun _ => .req .string) (some .string))]
    = true := by
  simp [unionOk, certAll]

/-! ### Arrays told apart by a literal position

The owner's witness. Each list below starts with a literal, and the empty list is an option of
its own. No phase of `Orth` separates any pair, and each pair meets at the bottom. -/

/-- The three options: a nonempty list of `"A"`, a nonempty list of `"B"`, and the empty list. -/
def literalListOptions : List Term :=
  [.list [.literal .string "A"] (some (.literal .string "A")) [],
   .list [.literal .string "B"] (some (.literal .string "B")) [],
   .list [] none []]

/-- `Orth` refuses each of the three pairs. -/
theorem orth_literalListOptions :
    literalListOptions.Pairwise (fun x y => Orth x y = false) := by decide

/-- **The meet certifies the union**: each pair meets at the bottom. -/
theorem unionOk_literalListOptions : unionOk literalListOptions = true := by decide

/-- **The crossing control is not certified.** `array (literal "A")` and `array (literal "B")`
    both hold `[]`, so the meet is `array never`, which holds `[]` and is not the bottom. -/
theorem not_unionOk_literalArrays :
    unionOk [.array (.literal .string "A"), .array (.literal .string "B")] = false := by decide

/-! ### Two literal sets, met through `each`

`Orth` certifies two string sets whose members are disjoint. The meet certifies the same pair,
because `each` meets `each` through the member sets, and no set has every element in an empty
meet. -/

/-- **Two string sets with disjoint members meet at the bottom.** -/
theorem meetNever_disjointStringSets :
    meetNever (.refine (.set .string) (.each (.members .string (NEFinset.of "a" {"b"}))))
      (.refine (.set .string) (.each (.members .string (NEFinset.of "c" ∅)))) = true := by
  decide

/-- **Two string sets that share a member meet at the set of the shared members.** -/
theorem meet_stringSets_shared :
    Term.meet (.refine (.set .string) (.each (.members .string (NEFinset.of "a" {"b"}))))
      (.refine (.set .string) (.each (.members .string (NEFinset.of "b" {"c"}))))
      = some (.refine (.set .string) (.each (.members .string (NEFinset.of "b" ∅)))) := by
  rfl

/-! ### The views certify a `held` whose caller side is precise

A string set held as a list of strings, beside a list of numbers. Both terms write the kind of a
list, so the occupancies meet. The caller-side views meet at the bottom when the caller side
requires one element or more, and the stored-side views differ in kind. -/

/-- The occupancies and the meet do not certify the pair. -/
theorem certPair_heldNE_base :
    (Orth (.held (.set .string) (.list [.string] (some .string) []) id id)
        (.list [] (some .number) [])
      || meetNever (.held (.set .string) (.list [.string] (some .string) []) id id)
        (.list [] (some .number) [])) = false := by
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

example : μSyn (Term.union [.string, .null]) = none := by simp [μSyn, μSynList, unanimous]

example : ¬ (μSyn Term.null = μSyn (Term.union [.string, .null])) := by
  simp [μSyn, μSynList, unanimous]

example : Term.meet .opaq .string = some .string := by rfl

/-! ### `lazy` is transparent, and it constrains nothing

`Term.lazy` carries a plain `Term`, not a closure, so the admission of `.lazy t` is the
admission of `t` on both halves (`ExactV.lean` and `ExactA.lean`). The meet reads through the
thunk on either side. `μSyn (.lazy t)` is `none`, so a `lazy` factor names no member and
constrains nothing, exactly as an `opaq` factor does: the answer comes back unwrapped. -/

/-- Two thunks over disjoint bases share no value. -/
example : Term.meet (.lazy .string) (.lazy .number) = some .never := by rfl

/-- The thunk is transparent on the left alone. -/
example : Term.meet (.lazy .string) .number = some .never := by rfl

/-- The `opaq` rule: the `lazy` factor names no member, so the meet takes the other factor's
    answer without the wrapper. -/
example : Term.meet (.lazy .string) .string = some .string := by rfl

/-- `held` still refuses, and the ground is its alone: it carries host
    functions (`Term.lean`), so no term states the intersection of two of them. -/
example : Term.meet (.held .string .opaq (fun v => v) (fun v => v)) .string = none := by rfl

example : ¬ (μSyn Term.string = μSyn Term.opaq) := by simp [μSyn]

/-! ## The homomorphism

`Adm` carries the meet to conjunction. The proof mirrors the definition's three layers. One
shared lemma covers `meetSRight`, parametric in the family. One flat lemma covers each family.
The outer statement recurses structurally on the left operand. The lemmas each class needs are
stated first.
-/


/-! ## The levers -/

/-! ## What `opaque` admits

`Adm .opaq v` is `dom(e)` of `opaqCodecω`, and a scalar's budget is one layer, so each
row below is the corresponding unfolding at fuel `0+1`. -/

/-- `opaque` writes every string, so `string` is the finer term. -/
theorem Adm_opaq_str (s : String) : Adm .opaq (.str s) = true := by
  show ((opaqCodec (Value.depth (.str s))).e (.str s)).isSome = true
  rw [show Value.depth (.str s) = 0 + 1 from rfl, opaqCodec_e_str]
  simp [stringCodec]

/-- …every boolean. -/
theorem Adm_opaq_bool (b : Bool) : Adm .opaq (.bool b) = true := by
  show ((opaqCodec (Value.depth (.bool b))).e (.bool b)).isSome = true
  rw [show Value.depth (.bool b) = 0 + 1 from rfl, opaqCodec_e_bool]
  simp [booleanCodec]

/-- …every byte string. -/
theorem Adm_opaq_bin (b : Bytes) : Adm .opaq (.bin b) = true := by
  show ((opaqCodec (Value.depth (.bin b))).e (.bin b)).isSome = true
  rw [show Value.depth (.bin b) = 0 + 1 from rfl, opaqCodec_e_bin]
  simp [binaryCodec]

/-- …and the null point. -/
theorem Adm_opaq_null : Adm .opaq .null = true := by
  show ((opaqCodec (Value.depth .null)).e .null).isSome = true
  rw [show Value.depth .null = 0 + 1 from rfl, opaqCodec_e_null]
  simp [nullCodec]

/-- …and every numeral, exactly on `D`. -/
theorem Adm_opaq_num (d : WFNumeral) :
    Adm .opaq (.num d) = inD (.num d) := by
  show ((opaqCodec (Value.depth (.num d))).e (.num d)).isSome = _
  rw [show Value.depth (.num d) = 0 + 1 from rfl, opaqCodec_e_num]
  simp [numberCodec, inD]


/-- Two terms whose occupancies are disjoint share no value, so their conjunction is the
    bottom. This closes every row that answers `never` because the two write different
    `Value` constructors. -/
theorem Adm_and_false {x y : Term} (h : Orth1 x y = true) (v : Value) :
    (Adm x v && Adm y v) = false := by
  cases hx : Adm x v with
  | false => simp
  | true =>
    cases hy : Adm y v with
    | false => simp
    | true =>
      have h2 := occV_disjoint_of_Orth1 h (occV_sound x v hx)
      rw [occV_sound y v hy] at h2
      exact absurd h2 (by simp)

/-! The four whose admission is a function. On the left they refuse at every partner but the
    bottom; on the right the same, and the left rows fire first so only `never` needs naming. -/

/-- **A key set's row splits where its body is a conjunction**, which is the shape the object
    rows leave. Named rather than left to a tactic, for the reason the set rows give. -/
theorem decide_forall_and {α : Sort*} {p q r : α → Bool}
    [Decidable (∀ k, r k = true)] [Decidable (∀ k, p k = true)] [Decidable (∀ k, q k = true)]
    (h : ∀ k, r k = (p k && q k)) :
    decide (∀ k, r k = true) = (decide (∀ k, p k = true) && decide (∀ k, q k = true)) := by
  simp only [h, Bool.and_eq_true, forall_and]
  simp

/-- A list of answers that all succeeded pairs each source with its answer. -/
theorem allSome_map_forall₂ {α β : Type} (f : α → Option β) :
    ∀ {xs : List α} {ys : List β}, allSome (xs.map f) = some ys →
      List.Forall₂ (fun x y => f x = some y) xs ys := by
  intro xs
  induction xs with
  | nil => intro ys h; simp only [List.map_nil, allSome, Option.some.injEq] at h; subst h; exact .nil
  | cons a as ihx =>
    intro ys h
    rw [List.map_cons] at h
    cases hf : f a with
    | none => rw [hf] at h; simp only [allSome, reduceCtorEq] at h
    | some b =>
      rw [hf] at h
      simp only [allSome, Option.map_eq_some_iff] at h
      obtain ⟨zs, hzs, rfl⟩ := h
      exact .cons hf (ihx hzs)

/-- Two tuples of one arity: the positions meet positionwise and the tails meet. -/
theorem alignP_meet_zip :
    ∀ {Ps Qs Rs : List VP},
      List.Forall₂ (fun (pq : VP × VP) r => ∀ w, r w = (pq.1 w && pq.2 w)) (Ps.zip Qs) Rs →
      Ps.length = Qs.length →
    ∀ {pt qt rt : Option VP},
      ((pt = none ∧ qt = none ∧ rt = none) ∨
        ∃ p q r, pt = some p ∧ qt = some q ∧ rt = some r ∧ ∀ w, r w = (p w && q w)) →
    ∀ ws, alignP Rs rt ws = (alignP Ps pt ws && alignP Qs qt ws) := by
  intro Ps Qs Rs hF hlen pt qt rt htl ws
  induction ws generalizing Ps Qs Rs with
  | nil =>
    cases Ps with
    | nil =>
      cases Qs with
      | nil =>
        cases hF
        rcases htl with ⟨rfl, rfl, rfl⟩ | ⟨p, q, r, rfl, rfl, rfl, _⟩ <;> simp [alignP]
      | cons => simp only [List.length_nil, List.length_cons] at hlen; omega
    | cons p Ps' =>
      cases Qs with
      | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
      | cons q Qs' =>
        rw [List.zip_cons_cons] at hF
        cases hF with
        | cons _ _ => simp [alignP]
  | cons w ws ihw =>
    cases Ps with
    | nil =>
      cases Qs with
      | nil =>
        cases hF
        rcases htl with ⟨rfl, rfl, rfl⟩ | ⟨p, q, r, rfl, rfl, rfl, hr⟩
        · simp [alignP]
        · simp only [alignP, hr, ihw (Ps := []) (Qs := []) .nil rfl]
          simp [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]
      | cons => simp only [List.length_nil, List.length_cons] at hlen; omega
    | cons p Ps' =>
      cases Qs with
      | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
      | cons q Qs' =>
        rw [List.zip_cons_cons] at hF
        cases hF with
        | cons hr hrest =>
          simp only [alignP, hr, ihw hrest (by simpa using hlen)]
          simp [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]

/-- A tuple with no tail pins the length of the array it admits. -/
theorem alignP_none_length : ∀ {Ps : List VP} {ws : List Value},
    alignP Ps none ws = true → ws.length = Ps.length := by
  intro Ps
  induction Ps with
  | nil => intro ws h; cases ws with
    | nil => rfl
    | cons _ _ => simp [alignP] at h
  | cons p Ps' ihp =>
    intro ws h
    cases ws with
    | nil => simp [alignP] at h
    | cons w ws' =>
      simp only [alignP, Bool.and_eq_true] at h
      simp [ihp h.2]


/-- The rows of a term list are that list mapped, so `rowOfG_map` carries a row of terms
    onto the row of rows the admission reads. -/
theorem AdmList_eq_map (ts : List Term) : AdmList ts = ts.map Adm := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [AdmList, List.map_cons, ih]

/-- …and the same for the spread. -/
theorem AdmOptT_eq_map (sp : Option Term) : AdmOptT sp = sp.map Adm := by
  cases sp <;> rfl

/-- **The suffix row meets position by position**, which is `alignP_meet_zip` for the half
    that carries no spread. Stated over terms, because the three rows the `list` meet
    compares are rows of terms. -/
theorem zipP_meet {r₁ r₂ rz : List Term} (hlen : r₁.length = r₂.length)
    (hF : List.Forall₂ (fun (pq : Term × Term) w => ∀ u, Adm w u = (Adm pq.1 u && Adm pq.2 u))
      (r₁.zip r₂) rz) :
    ∀ ws, zipP (AdmList rz) ws = (zipP (AdmList r₁) ws && zipP (AdmList r₂) ws) := by
  intro ws
  induction ws generalizing r₁ r₂ rz with
  | nil =>
      cases r₁ with
      | nil =>
          cases r₂ with
          | nil => cases hF; simp [zipP, AdmList]
          | cons => simp only [List.length_nil, List.length_cons] at hlen; omega
      | cons t r₁' =>
          cases r₂ with
          | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
          | cons u r₂' =>
              rw [List.zip_cons_cons] at hF
              cases hF with
              | cons _ _ => simp [zipP, AdmList]
  | cons w ws ihw =>
      cases r₁ with
      | nil =>
          cases r₂ with
          | nil => cases hF; simp [zipP, AdmList]
          | cons => simp only [List.length_nil, List.length_cons] at hlen; omega
      | cons t r₁' =>
          cases r₂ with
          | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
          | cons u r₂' =>
              rw [List.zip_cons_cons] at hF
              cases hF with
              | cons hr hrest =>
                  simp only [AdmList, zipP, hr,
                    ihw (by simpa using hlen) hrest]
                  simp [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]

/-- `opaque`'s row is `dom(e)` of its codec, budgeted by the value's own depth. -/
theorem Adm_opaq_eq (v : Value) :
    Adm .opaq v = ((opaqCodec (Value.depth v)).e v).isSome := rfl

/-- A body admits nothing that is not a map. -/
theorem AdmBody_of_not_map {c : Body} {v : Value} (h : ∀ keys g, v ≠ .map keys g) :
    AdmBody c v = false := by
  cases c with
  | mk fields fld wild =>
    cases v with
    | map keys g => exact absurd rfl (h keys g)
    | _ => rfl

/-- The bottom is the only term that reads as the bottom. -/
theorem eq_never_of_isNever {t : Term} (h : t.isNever = true) : t = .never := by
  cases t <;> simp only [Term.isNever, Bool.false_eq_true] at h <;> rfl

/-- Normalising a refinement keeps the member it stores, because the bottom stores none and so
    does the refinement over it. -/
theorem μSyn_refineOf {z : Term} {p : Pred} {m : Member}
    (h : μSyn (Term.refineOf z p) = some m) : μSyn z = some m := by
  cases z <;>
    first
      | exact h
      | (simp only [Term.refineOf] at h
         split at h
         · simpa [μSyn] using h
         · exact absurd h (by simp [μSyn])
         · exact h)

/-- A declared position that holds nothing empties the tuple: every list the tuple admits fills
    each declared position. -/
theorem alignP_never_false : ∀ {ts : List Term} {tail : Option Term} {ws : List Value},
    ts.any Term.isNever = true → alignP (AdmList ts) (AdmOptT tail) ws = false := by
  intro ts
  induction ts with
  | nil => intro _ _ h; simp at h
  | cons t ts' ih =>
    intro tail ws h
    cases ws with
    | nil => rfl
    | cons w ws' =>
      simp only [List.any_cons, Bool.or_eq_true] at h
      simp only [AdmList, alignP]
      rcases h with ht | hrest
      · rw [show t = Term.never from eq_never_of_isNever ht, show Adm .never _ = false from rfl, Bool.false_and]
      · rw [ih (tail := tail) (ws := ws') hrest, Bool.and_false]

/-- A declared SUFFIX position that holds nothing empties the list, for the same reason:
    every value the list admits fills each suffix position too. -/
theorem zipP_never_false : ∀ {suf : List Term} {ws : List Value},
    suf.any Term.isNever = true → zipP (AdmList suf) ws = false := by
  intro suf
  induction suf with
  | nil => intro _ h; simp at h
  | cons t ts' ih =>
    intro ws h
    cases ws with
    | nil => rfl
    | cons w ws' =>
      simp only [List.any_cons, Bool.or_eq_true] at h
      simp only [AdmList, zipP]
      rcases h with ht | hrest
      · rw [show t = Term.never from eq_never_of_isNever ht,
          show Adm .never w = false from rfl, Bool.false_and]
      · rw [ih (ws := ws') hrest, Bool.and_false]

/-- Normalising a list keeps what it admits. -/
theorem Adm_listOf (pre : List Term) (sp : Option Term) (suf : List Term) (v : Value) :
    Adm (Term.listOf pre sp suf) v = Adm (.list pre sp suf) v := by
  unfold Term.listOf
  split
  next hany =>
    cases v <;> simp only [Adm] <;> try rfl
    rename_i ws
    refine Eq.symm ?_
    simp only [alignPL]
    rcases Bool.or_eq_true .. |>.mp hany with hp | hs
    · rw [alignP_never_false hp, Bool.false_and]
    · rw [zipP_never_false hs, Bool.and_false]
  next => rfl

/-- **The `list` meet's whole admission obligation, read off the three rows.** A `list`
    admits an array exactly where its row at that length does, so an answer whose row exists
    exactly where both factors' rows exist, and is their pointwise meet there, admits exactly
    what both factors admit. Each of `listMeetRow`'s three branches supplies these two facts
    and nothing else. -/
theorem Adm_list_rows {p₁ s₁ p₂ s₂ pz sz : List Term} {q₁ q₂ qz : Option Term}
    (hsome : ∀ n, (rowOfG pz qz sz n).isSome
      = ((rowOfG p₁ q₁ s₁ n).isSome && (rowOfG p₂ q₂ s₂ n).isSome))
    (hrel : ∀ n r₁ r₂ rz, rowOfG p₁ q₁ s₁ n = some r₁ → rowOfG p₂ q₂ s₂ n = some r₂ →
      rowOfG pz qz sz n = some rz →
      r₁.length = r₂.length ∧
        List.Forall₂ (fun (pq : Term × Term) w => ∀ u, Adm w u = (Adm pq.1 u && Adm pq.2 u))
          (r₁.zip r₂) rz)
    (v : Value) :
    Adm (.list pz qz sz) v = (Adm (.list p₁ q₁ s₁) v && Adm (.list p₂ q₂ s₂) v) := by
  cases v with
  | arr ws =>
      have hb := hsome ws.length
      simp only [Adm, AdmList_eq_map, AdmOptT_eq_map, alignPL_eq_rowOfG, rowOfG_map]
      cases h₁ : rowOfG p₁ q₁ s₁ ws.length with
      | none =>
          rw [h₁] at hb
          simp only [Option.isSome_none, Bool.false_and] at hb
          cases hz : rowOfG pz qz sz ws.length with
          | none => simp
          | some rz => rw [hz] at hb; simp at hb
      | some r₁ =>
          cases h₂ : rowOfG p₂ q₂ s₂ ws.length with
          | none =>
              rw [h₁, h₂] at hb
              simp only [Option.isSome_some, Option.isSome_none, Bool.and_false] at hb
              cases hz : rowOfG pz qz sz ws.length with
              | none => simp
              | some rz => rw [hz] at hb; simp at hb
          | some r₂ =>
              cases hz : rowOfG pz qz sz ws.length with
              | none => rw [h₁, h₂, hz] at hb; simp at hb
              | some rz =>
                  obtain ⟨hlen, hF⟩ := hrel _ _ _ _ h₁ h₂ hz
                  simp only [Option.map_some]
                  simpa only [← AdmList_eq_map] using zipP_meet hlen hF ws
  | _ => simp [Adm]

/-- **Two `list` shapes with no common length share no value.** The bottom is the right
    answer exactly there, and `listMeetRow` reaches it from both flattening branches. -/
theorem Adm_list_disjoint {p₁ s₁ p₂ s₂ : List Term} {q₁ q₂ : Option Term}
    (h : ∀ n, rowOfG p₁ q₁ s₁ n = none ∨ rowOfG p₂ q₂ s₂ n = none) (v : Value) :
    (Adm (.list p₁ q₁ s₁) v && Adm (.list p₂ q₂ s₂) v) = false := by
  cases v with
  | arr ws =>
      simp only [Adm, AdmList_eq_map, AdmOptT_eq_map, alignPL_eq_rowOfG, rowOfG_map]
      rcases h ws.length with hn | hn <;> simp [hn]
  | _ => simp [Adm]

/-- Normalising a tuple keeps what it admits. -/
theorem Adm_tupleOf (ts : List Term) (tail : Option Term) (v : Value) :
    Adm (Term.tupleOf ts tail) v = Adm (.tuple ts tail) v :=
  Adm_listOf ts tail [] v

/-- …and normalising a refinement keeps what it admits. -/
theorem Adm_refineOf (z : Term) (p : Pred) (v : Value) :
    Adm (Term.refineOf z p) v = Adm (.refine z p) v := by
  cases z <;>
    first
      | rfl
      | (simp only [Term.refineOf]
         rename_i z' q
         split
         · rename_i r hr
           show (Adm z' v && Pred.eval r v) = ((Adm z' v && Pred.eval q v) && Pred.eval p v)
           rw [meetM_eval hr v, Bool.and_assoc]
         · rename_i hr
           show false = ((Adm z' v && Pred.eval q v) && Pred.eval p v)
           rw [Bool.and_assoc, meetM_empty hr v, Bool.and_false]
         · rfl)

/-- A field that admits nothing at a name that must be present is a field that must be present. -/
theorem isReq_of_isBottom {f : ObjectSlot} (h : ObjectSlot.isBottom f = true) : ObjectSlot.isReq f = true := by
  cases f <;> simp only [ObjectSlot.isBottom, ObjectSlot.isReq, Bool.false_eq_true] at h ⊢

/-- …and it admits no value at all. -/
theorem AdmField_of_isBottom {f : ObjectSlot} (h : ObjectSlot.isBottom f = true) (w : Value) :
    AdmField f w = false := by
  cases f with
  | req t => rw [show t = .never from eq_never_of_isNever h]; rfl
  | optional t => exact absurd h (by simp [ObjectSlot.isBottom])

/-- A list admits a value exactly when one of its terms does. -/
theorem AdmAny_iff : ∀ {os : List Term} {v : Value},
    AdmAny os v = true ↔ ∃ t ∈ os, Adm t v = true
  | [], v => by simp
  | t :: ts, v => by
      rw [AdmAny_cons, Bool.or_eq_true, AdmAny_iff]
      constructor
      · rintro (h | ⟨u, hu, h⟩)
        · exact ⟨t, by simp, h⟩
        · exact ⟨u, by simp [hu], h⟩
      · rintro ⟨u, hu, h⟩
        rcases List.mem_cons.mp hu with rfl | hu'
        · exact Or.inl h
        · exact Or.inr ⟨u, hu', h⟩


/-! ### The count, and what the meet does to it

These are what let the coproduct row of the meet stand without a certificate. The guard on that
row used to supply one, and the guard could not survive: the certificate is stated on the meet,
so a guard that consults it closes a cycle. What the row actually needs is that the meet scales
the number of admitting options by whether the partner admits, and that is a fact about counting
rather than about separation. -/

/-- A term that admits a value is not the bottom. -/
theorem not_isNever_of_adm {t : Term} {v : Value} (h : Adm t v = true) : t.isNever = false := by
  cases ht : t.isNever with
  | true =>
      rw [eq_never_of_isNever ht, show Adm .never v = false from rfl] at h
      exact absurd h (by simp)
  | false => rfl

/-- A list reads an attribute exactly when one of its terms does. -/
theorem AdmAAny_iff : ∀ {os : List Term} {a : Attr},
    AdmAAny os a = true ↔ ∃ t ∈ os, AdmA t a = true
  | [], a => by simp
  | t :: ts, a => by
      rw [AdmAAny_cons, Bool.or_eq_true, AdmAAny_iff]
      constructor
      · rintro (h | ⟨u, hu, h⟩)
        · exact ⟨t, by simp, h⟩
        · exact ⟨u, by simp [hu], h⟩
      · rintro ⟨u, hu, h⟩
        rcases List.mem_cons.mp hu with rfl | hu'
        · exact Or.inl h
        · exact Or.inr ⟨u, hu', h⟩

/-- The options that survive are the ones that admit; the bottoms admit nothing. -/
theorem AdmAny_filter_never : ∀ (ts : List Term) (v : Value),
    AdmAny (ts.filter (fun z => !z.isNever)) v = AdmAny ts v
  | [], _ => rfl
  | t :: ts, v => by
      cases ht : t.isNever with
      | true =>
        have htn : t = Term.never := eq_never_of_isNever ht
        subst htn
        rw [List.filter_cons, if_neg (by simp [Term.isNever]), AdmAny_cons,
          AdmAny_filter_never ts v]
        rfl
      | false =>
        rw [List.filter_cons, if_pos (by simp [ht]), AdmAny_cons, AdmAny_cons,
          AdmAny_filter_never ts v]

/-- The join over the met options is the join over the options, met with the partner. -/
theorem AdmAny_meet {y : Term} (v : Value) : ∀ {os zs : List Term},
    List.Forall₂ (fun t w => ∀ u, Adm w u = (Adm t u && Adm y u)) os zs →
    AdmAny zs v = (AdmAny os v && Adm y v) := by
  intro os zs h
  induction h with
  | nil => simp
  | cons hh _ ihx =>
    rw [AdmAny_cons, AdmAny_cons, hh v, ihx]
    cases Adm _ v <;> cases Adm y v <;> simp

/-- **`ofOptions` admits what its options admit**, and no certificate is spent. -/
theorem Adm_ofOptions (ts : List Term) (v : Value) :
    Adm (Term.ofOptions ts) v = AdmAny ts v := by
  match ts with
  | [] => rfl
  | [t] => simp only [Term.ofOptions, AdmAny_cons, AdmAny_nil, Bool.or_false]
  | _ :: _ :: _ => exact selOptV_eq_AdmAny _ v

/-- **The coproduct row of the meet needs no certificate.** The bottoms admit nothing, and `&&`
    distributes over the options' disjunction. -/
theorem union_meet_free {os zs : List Term} {y : Term} (v : Value)
    (hR : List.Forall₂ (fun t w => ∀ u, Adm w u = (Adm t u && Adm y u)) os zs) :
    Adm (Term.ofOptions (zs.filter (fun z => !z.isNever))) v
      = (Adm (.union os) v && Adm y v) := by
  rw [Adm_ofOptions, AdmAny_filter_never, AdmAny_meet v hR, Adm_union, selOptV_eq_AdmAny]

section StructuralAdm
-- the object rows put the whole field table to `decide` under a binder, which is where the
-- default budget goes
set_option maxHeartbeats 1000000

/-! ## `Adm` is a homomorphism from the meet to conjunction, structurally

The definition recurses on the left operand, so the theorem does too: one shared lemma for every
row that reads the right operand alone, one flat lemma per left constructor, and an outer
recursion that feeds the induction hypothesis at the subterm into the two. No measure appears,
and the depth bounds the well-founded proof carries are gone with it. -/

/-- The right operands `meetSRight` hands to the family: everything its own rows do not answer.
    A family's catch-all row answers the bottom, which is right for these and wrong for the
    seven above, so the predicate below carries the same split the definition makes. `lazy`
    stays outside, because its own row meets the subterm and hands the family no thunk. -/
def Delegated : Term → Prop
  | .never | .held _ _ _ _ | .lazy _ | .refine _ _ | .union _ => False
  | _ => True

/-- `f` answers the meet with one term fixed on the left, at EVERY right operand. The container
    families need this of the call they carry, because they apply it to a subterm of any shape. -/
def AdmSound (x : Term) (f : Term → Option Term) : Prop :=
  ∀ y z, f y = some z → ∀ v, Adm z v = (Adm x v && Adm y v)

/-- `fam` answers the meet with one term fixed on the left, over the operands it is handed. -/
def AdmFam (x : Term) (fam : Term → Option Term) : Prop :=
  ∀ y z, Delegated y → fam y = some z → ∀ v, Adm z v = (Adm x v && Adm y v)

/-- The list companion is the plain map, so the union row reuses the `Forall₂` machinery. -/
theorem meetSRightL_eq (fam : Term → Option Term) :
    ∀ os, meetSRightL fam os = os.map (meetSRight fam)
  | [] => rfl
  | _ :: os => congrArg _ (meetSRightL_eq fam os)

/-- …and the union row's extraction, with no exclusions: the row is reached by the pattern. -/
theorem meetSRight_union {fam : Term → Option Term} {os : List Term} {z : Term}
    (h : meetSRight fam (.union os) = some z) :
    ∃ zs, List.Forall₂ (fun t w => meetSRight fam t = some w) os zs ∧
      z = Term.ofOptions (zs.filter (fun w => !w.isNever)) := by
  rw [meetSRight] at h
  obtain ⟨zs, hzs, hg⟩ := Option.bind_eq_some_iff.mp h
  refine ⟨zs, allSome_map_forall₂ _ ?_, (Option.some.inj hg).symm⟩
  rw [← meetSRightL_eq]
  exact hzs

mutual
/-- Every row that reads the right operand alone is sound wherever the family is. -/
theorem Adm_meetSRight {x : Term} {fam : Term → Option Term} (hf : AdmFam x fam) :
    ∀ y z, meetSRight fam y = some z → ∀ v, Adm z v = (Adm x v && Adm y v)
  | .never, _, h, _ => by
      simp only [meetSRight, Option.some.injEq] at h; subst h; simp [Adm]
  | .held _ _ _ _, _, h, _ => by simp [meetSRight] at h
  | .lazy t, _, h, v => by
      rw [meetSRight] at h
      simpa [Adm] using Adm_meetSRight hf t _ h v
  | .refine y p, _, h, v => by
      simp only [meetSRight] at h
      split at h
      · obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
        have ihw := Adm_meetSRight hf y w hw v
        rw [Adm_refineOf]
        simp only [Adm, ihw]
        simp [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]
      · exact absurd h (by simp)
  | .union os, _, h, v => by
      obtain ⟨zs, hF, rfl⟩ := meetSRight_union h
      rw [Bool.and_comm]
      exact union_meet_free v (Adm_meetSRightL hf os _ hF)
  | .string, _, h, v => hf .string _ trivial h v
  | .number, _, h, v => hf .number _ trivial h v
  | .boolean, _, h, v => hf .boolean _ trivial h v
  | .binary, _, h, v => hf .binary _ trivial h v
  | .null, _, h, v => hf .null _ trivial h v
  | .literal k lv, _, h, v => hf (.literal k lv) _ trivial h v
  | .set b, _, h, v => hf (.set b) _ trivial h v
  | .opaq, _, h, v => hf .opaq _ trivial h v
  | .list p q s, _, h, v => hf (.list p q s) _ trivial h v
  | .object b, _, h, v => hf (.object b) _ trivial h v
termination_by structural y => y

/-- The list companion: the union row's options, lifted pointwise. It recurses on the list and
    `Adm_meetSRight` on the term, as the definition's own pair does. -/
theorem Adm_meetSRightL {x : Term} {fam : Term → Option Term} (hf : AdmFam x fam) :
    ∀ os zs, List.Forall₂ (fun t w => meetSRight fam t = some w) os zs →
      List.Forall₂ (fun t w => ∀ u, Adm w u = (Adm t u && Adm x u)) os zs
  | [], _, h => by cases h; exact .nil
  | t :: ts, _, h => by
      cases h with
      | cons hh ht =>
          exact .cons (fun u => by rw [Adm_meetSRight hf t _ hh u, Bool.and_comm])
            (Adm_meetSRightL hf ts _ ht)
termination_by structural os => os
end

/-- The catch-all of every family: two constructors in different value slots meet at the bottom. -/
theorem Adm_never_orth {x y : Term} (ho : Orth1 x y = true) (v : Value) :
    Adm Term.never v = (Adm x v && Adm y v) := by
  rw [Adm_and_false ho v]; simp [Adm]

/-- The tactic every family's catch-all row uses. -/
local macro "fam_never" fam:ident : tactic => `(tactic|
  (simp only [$fam:ident, Option.some.injEq] at *
   subst_vars
   refine Adm_never_orth ?_ _
   first
     | rfl
     | decide
     | (cases ‹GroundKind› <;> first | rfl | decide)
     | (cases ‹SetBase› <;> first | rfl | decide)
     | (cases ‹GroundKind› <;> cases ‹SetBase› <;> first | rfl | decide)))

/-- `boolean` meets the boolean literal, `opaque`, and nothing else. -/
theorem Adm_famBoolean : AdmFam Term.boolean famBoolean := by
  intro y z hd h v
  cases y <;> first | exact hd.elim | skip
  case boolean => simp only [famBoolean, Option.some.injEq] at h; subst h; simp
  case literal k v' =>
      simp only [famBoolean] at h
      split at h
      next hk =>
        subst hk
        simp only [Option.some.injEq] at h; subst h
        cases v <;> simp [Adm, AdmLit, inL, inD]
      next hk =>
        simp only [Option.some.injEq] at h; subst h
        cases k <;> cases v <;> simp_all [Adm, AdmLit, inL, inD]
  case opaq =>
      simp only [famBoolean, Option.some.injEq] at h; subst h
      cases v <;> (try simp only [Adm_opaq_bool]) <;> simp [Adm]
  all_goals fam_never famBoolean

/-- `binary` meets the binary literal, `opaque`, and nothing else. -/
theorem Adm_famBinary : AdmFam Term.binary famBinary := by
  intro y z hd h v
  cases y <;> first | exact hd.elim | skip
  case binary => simp only [famBinary, Option.some.injEq] at h; subst h; simp
  case literal k v' =>
      simp only [famBinary] at h
      split at h
      next hk =>
        subst hk
        simp only [Option.some.injEq] at h; subst h
        cases v <;> simp [Adm, AdmLit, inL, inD]
      next hk =>
        simp only [Option.some.injEq] at h; subst h
        cases k <;> cases v <;> simp_all [Adm, AdmLit, inL, inD]
  case opaq =>
      simp only [famBinary, Option.some.injEq] at h; subst h
      cases v <;> (try simp only [Adm_opaq_bin]) <;> simp [Adm]
  all_goals fam_never famBinary

/-- `null` meets the null literal, `opaque`, and nothing else. -/
theorem Adm_famNull : AdmFam Term.null famNull := by
  intro y z hd h v
  cases y <;> first | exact hd.elim | skip
  case null => simp only [famNull, Option.some.injEq] at h; subst h; simp
  case literal k v' =>
      simp only [famNull] at h
      split at h
      next hk =>
        subst hk
        simp only [Option.some.injEq] at h; subst h
        cases v <;> simp [Adm, AdmLit, inL, inD]
      next hk =>
        simp only [Option.some.injEq] at h; subst h
        cases k <;> cases v <;> simp_all [Adm, AdmLit, inL, inD]
  case opaq =>
      simp only [famNull, Option.some.injEq] at h; subst h
      cases v <;> (try simp only [Adm_opaq_null]) <;> simp [Adm]
  all_goals fam_never famNull

/-- `string` meets its own literals and `opaque`. -/
theorem Adm_famString : AdmFam Term.string famString := by
  intro y z hd h v
  cases y <;> first | exact hd.elim | skip
  case string => simp only [famString, Option.some.injEq] at h; subst h; simp
  case literal k v' =>
      cases k <;> simp only [famString, Option.some.injEq, reduceCtorEq] at h <;>
        (try subst h) <;>
        first
          | (cases v <;> simp [Adm, AdmLit, inL, inD] <;>
              (try (intro hs _; exact hs)))
          | exact Adm_never_orth (by rfl) v
  case opaq =>
      simp only [famString, Option.some.injEq] at h; subst h
      cases v <;> (try simp only [Adm_opaq_str]) <;> simp [Adm]
  all_goals fam_never famString

/-- `number` meets its own literals and `opaque`. -/
theorem Adm_famNumber : AdmFam Term.number famNumber := by
  intro y z hd h v
  cases y <;> first | exact hd.elim | skip
  case number => simp only [famNumber, Option.some.injEq] at h; subst h; simp
  case literal k v' =>
      cases k <;> simp only [famNumber, Option.some.injEq, reduceCtorEq] at h <;>
        (try subst h) <;>
        first
          | (cases v <;> simp [Adm, AdmLit, inL, inD] <;>
              (try (intro hs _; exact hs)))
          | exact Adm_never_orth (by rfl) v
  case opaq =>
      simp only [famNumber] at h
      simp only [Option.some.injEq] at h; subst h
      cases v <;> (try simp only [Adm_opaq_num]) <;> simp [Adm, inD]
  all_goals fam_never famNumber

/-- A literal meets its own base and an equal literal, and is the bottom elsewhere. -/
theorem Adm_famLit (k : GroundKind) (lv : k.Carrier) : AdmFam (.literal k lv) (famLit k lv) := by
  intro y z hd h v
  cases y <;> first | exact hd.elim | skip
  case string | number =>
      cases k <;> simp only [famLit, Option.some.injEq, reduceCtorEq] at h <;>
        (try subst h) <;>
        first
          | (cases v <;> simp [Adm, AdmLit, inL, inD] <;>
              (try (intro hs _; exact hs)))
          | exact Adm_never_orth (by rfl) v
  case boolean | binary | null =>
      simp only [famLit] at h
      split at h
      next hk =>
        subst hk
        simp only [Option.some.injEq] at h; subst h
        cases v <;> simp [Adm, AdmLit, inL, inD]
      next hk =>
        simp only [Option.some.injEq] at h; subst h
        cases k <;> cases v <;> simp_all [Adm, AdmLit, inL, inD]
  case literal k' v' =>
      simp only [famLit] at h
      cases k <;> cases k' <;> simp only [Term.meetLit, reduceCtorEq] at h <;>
        (try split at h) <;>
        (try (simp only [Option.some.injEq] at h
              subst h
              cases v <;> simp_all [Adm, AdmLit, inL, inD]))
  case opaq => simp [famLit] at h
  all_goals fam_never famLit

/-- Two set bases meet where they are equal, and at the bottom wherever they occupy different
    wire slots. `famSet` refuses the rest, so every unequal row that reaches here has disjoint
    occupancy and `Adm_never_orth` is the whole argument, as it is for every other family. -/
theorem Adm_famSet (b : SetBase) : AdmFam (.set b) (famSet b) := by
  intro y z hd h v
  cases y <;> first | exact hd.elim | skip
  case set b' =>
      cases b <;> cases b' <;>
        simp only [famSet, reduceCtorEq, reduceIte, Option.some.injEq] at h <;>
        (try subst h) <;>
        first
          | simp
          | exact Adm_never_orth (by decide) v
  case opaq => simp [famSet] at h
  all_goals fam_never famSet

/-- `opaque` meets each self-identifying base, and another `opaque`. -/
theorem Adm_famOpaq : AdmFam .opaq (famOpaq) := by
  intro y z hd h v
  cases y <;> first | exact hd.elim | skip
  case string | boolean | binary | null =>
      simp only [famOpaq, Option.some.injEq] at h; subst h
      cases v <;>
        (try simp only [Adm_opaq_str, Adm_opaq_bool, Adm_opaq_bin, Adm_opaq_null]) <;>
        simp [Adm]
  case number =>
      simp only [famOpaq] at h
      simp only [Option.some.injEq] at h; subst h
      cases v <;> (try simp only [Adm_opaq_num]) <;> simp [Adm, inD]
  case opaq =>
      simp only [famOpaq, Option.some.injEq] at h; subst h
      exact (Bool.and_self _).symm
  all_goals simp [famOpaq] at h

/-! ### The container families. The depth bounds go: the lifts are measure-free. -/

/-- …and the same two tuples' positions zipped. -/
theorem zipF_lift :
    ∀ {ts us : List Term} {fs : List (Term → Option Term)} {vs : List Term},
      List.Forall₂ AdmSound ts fs →
      List.Forall₂ (fun (p : (Term → Option Term) × Term) v => p.1 p.2 = some v) (fs.zip us) vs →
      List.Forall₂ (fun (pq : VP × VP) r => ∀ w, r w = (pq.1 w && pq.2 w))
        ((AdmList ts).zip (AdmList us)) (AdmList vs) := by
  intro ts
  induction ts with
  | nil => intro us fs vs hfs hv; cases hfs; cases hv; exact .nil
  | cons t ts ihs =>
      intro us fs vs hfs hv
      cases hfs with
      | cons hf hfs' =>
          cases us with
          | nil => cases hv; exact .nil
          | cons u us =>
              cases hv with
              | cons hh ht => exact .cons (fun w => hf u _ hh w) (ihs hfs' ht)

/-- …and the zip companion is the plain map over the zip. -/
theorem zipF_eq : ∀ (fs : List (Term → Option Term)) (us : List Term),
    zipF fs us = (fs.zip us).map (fun p => p.1 p.2)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: fs, _ :: us => congrArg _ (zipF_eq fs us)

/-- Two rows of terms, the left as partially applied meets, met position by position. The
    term-level twin of `zipF_lift`, because the rows the `list` meet compares are rows of
    terms rather than rows of predicates. -/
theorem zipF_lift_terms :
    ∀ {ts us : List Term} {fs : List (Term → Option Term)} {vs : List Term},
      List.Forall₂ AdmSound ts fs →
      List.Forall₂ (fun (p : (Term → Option Term) × Term) v => p.1 p.2 = some v) (fs.zip us) vs →
      List.Forall₂ (fun (pq : Term × Term) w => ∀ u, Adm w u = (Adm pq.1 u && Adm pq.2 u))
        (ts.zip us) vs := by
  intro ts
  induction ts with
  | nil => intro us fs vs hfs hv; cases hfs; cases hv; exact .nil
  | cons t ts ihs =>
      intro us fs vs hfs hv
      cases hfs with
      | cons hsound hfs' =>
          cases us with
          | nil => cases hv; exact .nil
          | cons u us =>
              cases hv with
              | cons hh ht =>
                  exact .cons (fun w => hsound u _ hh w) (ihs hfs' ht)

/-- **The one positional container's family.** Two `list` shapes meet through their rows, and
    `Adm_list_rows` states the whole obligation over those rows. -/
theorem Adm_famList {pre suf : List Term} {sp : Option Term}
    {fpre fsuf : List (Term → Option Term)} {fsp : Option (Term → Option Term)}
    (hp : List.Forall₂ AdmSound pre fpre)
    (hs : (sp = none ∧ fsp = none) ∨ ∃ t f, sp = some t ∧ fsp = some f ∧ AdmSound t f)
    (hf : List.Forall₂ AdmSound suf fsuf) :
    AdmFam (.list pre sp suf) (famList fpre fsp fsuf) := by
  have hlp := hp.length_eq
  have hlf := hf.length_eq
  intro y z hd h v
  cases y <;> first | exact hd.elim | skip
  case list pre₂ sp₂ suf₂ =>
      simp only [famList] at h
      rcases hs with ⟨rfl, rfl⟩ | ⟨t, f, rfl, rfl, hsound⟩
      · -- The left states a fixed arity, so the answer is that one row, flattened.
        simp only [listMeetRow] at h
        rw [show rowOfG fpre none fsuf (fpre.length + fsuf.length) = some (fpre ++ fsuf) from
          by rw [rowOfG_none_eq, if_pos rfl]] at h
        have hlen0 : fpre.length + fsuf.length = pre.length + suf.length := by omega
        rw [hlen0] at h
        cases hR : rowOfG pre₂ sp₂ suf₂ (pre.length + suf.length) with
        | none =>
            rw [hR] at h
            simp only [Option.some.injEq] at h
            subst h
            have hdis : ∀ n, rowOfG pre none suf n = none ∨ rowOfG pre₂ sp₂ suf₂ n = none := by
              intro n
              cases hd : decide (n = pre.length + suf.length) with
              | true => simp only [decide_eq_true_eq] at hd; subst hd; exact Or.inr hR
              | false =>
                  simp only [decide_eq_false_iff_not] at hd
                  exact Or.inl (by rw [rowOfG_none_eq, if_neg hd])
            exact (Adm_list_disjoint hdis v).symm
        | some us =>
            rw [hR] at h
            obtain ⟨row, hrow, rfl⟩ := Option.map_eq_some_iff.mp h
            have hus : us.length = pre.length + suf.length := rowOfG_length hR
            have hFz : List.Forall₂
                (fun (p : (Term → Option Term) × Term) w => p.1 p.2 = some w)
                ((fpre ++ fsuf).zip us) row :=
              allSome_map_forall₂ _ (by rw [← zipF_eq]; exact hrow)
            have hrowlen : row.length = pre.length + suf.length := by
              have hz := hFz.length_eq
              simp only [List.length_zip, List.length_append, hus] at hz
              omega
            have hrel₀ := zipF_lift_terms (forall₂_append hp hf) hFz
            rw [Adm_listOf]
            refine Adm_list_rows (p₁ := pre) (q₁ := none) (s₁ := suf) ?_ ?_ v
            · intro n
              simp only [rowOfG_none_eq, List.length_nil, Nat.add_zero, hrowlen]
              cases hd : decide (n = pre.length + suf.length) with
              | true =>
                  simp only [decide_eq_true_eq] at hd
                  subst hd
                  rw [if_pos rfl, if_pos rfl, hR]
                  simp
              | false =>
                  simp only [decide_eq_false_iff_not] at hd
                  rw [if_neg hd, if_neg hd]
                  simp
            · intro n r₁ r₂ rz h1 h2 h3
              rw [rowOfG_none_eq] at h1 h3
              simp only [List.length_nil, Nat.add_zero, hrowlen] at h3
              split at h1
              · next he =>
                  simp only [Option.some.injEq] at h1
                  subst h1
                  subst he
                  rw [if_pos rfl] at h3
                  simp only [Option.some.injEq] at h3
                  subst h3
                  rw [hR] at h2
                  simp only [Option.some.injEq] at h2
                  subst h2
                  exact ⟨by simp only [List.length_append]; omega, by simpa using hrel₀⟩
              · exact absurd h1 (by simp)
      · cases sp₂ with
        | none =>
            -- The right states a fixed arity: the answer flattens to that length.
            simp only [listMeetRow] at h
            rw [show rowOfG pre₂ none suf₂ (pre₂.length + suf₂.length)
                = some (pre₂ ++ suf₂) from by rw [rowOfG_none_eq, if_pos rfl]] at h
            cases hL : rowOfG fpre (some f) fsuf (pre₂.length + suf₂.length) with
            | none =>
                rw [hL] at h
                simp only [Option.some.injEq] at h
                subst h
                have hshort : pre₂.length + suf₂.length < fpre.length + fsuf.length := by
                  rw [rowOfG_some_eq] at hL
                  split at hL
                  · omega
                  · exact absurd hL (by simp)
                have hdis : ∀ n,
                    rowOfG pre (some t) suf n = none ∨ rowOfG pre₂ none suf₂ n = none := by
                  intro n
                  cases hd : decide (n = pre₂.length + suf₂.length) with
                  | true =>
                      simp only [decide_eq_true_eq] at hd
                      subst hd
                      exact Or.inl (by rw [rowOfG_some_eq, if_pos (by omega)])
                  | false =>
                      simp only [decide_eq_false_iff_not] at hd
                      exact Or.inr (by rw [rowOfG_none_eq, if_neg hd])
                exact (Adm_list_disjoint hdis v).symm
            | some fs =>
                rw [hL] at h
                obtain ⟨row, hrow, rfl⟩ := Option.map_eq_some_iff.mp h
                obtain ⟨ts, hts, htsF⟩ :=
                  rowOfG_forall₂_left hp (Or.inr ⟨t, f, rfl, rfl, hsound⟩) hf hL
                have hmin : pre.length + suf.length ≤ pre₂.length + suf₂.length := by
                  rw [rowOfG_some_eq] at hL
                  split at hL
                  · exact absurd hL (by simp)
                  · omega
                have hfs : fs.length = pre₂.length + suf₂.length := rowOfG_length hL
                have hFz : List.Forall₂
                    (fun (p : (Term → Option Term) × Term) w => p.1 p.2 = some w)
                    (fs.zip (pre₂ ++ suf₂)) row :=
                  allSome_map_forall₂ _ (by rw [← zipF_eq]; exact hrow)
                have hrowlen : row.length = pre₂.length + suf₂.length := by
                  have hz := hFz.length_eq
                  simp only [List.length_zip, List.length_append, hfs] at hz
                  omega
                have hrel₀ := zipF_lift_terms htsF hFz
                rw [Adm_listOf]
                refine Adm_list_rows (p₁ := pre) (q₁ := some t) (s₁ := suf) ?_ ?_ v
                · intro n
                  simp only [rowOfG_none_eq, rowOfG_some_eq, List.length_nil, Nat.add_zero,
                    hrowlen]
                  cases hd : decide (n = pre₂.length + suf₂.length) with
                  | true =>
                      simp only [decide_eq_true_eq] at hd
                      subst hd
                      rw [if_pos rfl, if_neg (by omega), if_pos rfl]
                      simp
                  | false =>
                      simp only [decide_eq_false_iff_not] at hd
                      rw [if_neg hd, if_neg hd]
                      simp
                · intro n r₁ r₂ rz h1 h2 h3
                  rw [rowOfG_none_eq] at h2 h3
                  simp only [List.length_nil, Nat.add_zero, hrowlen] at h3
                  split at h2
                  · next he =>
                      simp only [Option.some.injEq] at h2
                      subst h2
                      subst he
                      rw [if_pos rfl] at h3
                      simp only [Option.some.injEq] at h3
                      subst h3
                      rw [hts] at h1
                      simp only [Option.some.injEq] at h1
                      subst h1
                      refine ⟨?_, by simpa using hrel₀⟩
                      have hl := rowOfG_length hts
                      simp only [List.length_append]
                      omega
                  · exact absurd h2 (by simp)
        | some c =>
            -- Both sides spread. The answer is the row at one length, re-spread at every
            -- other, and `dominates` is what makes the answer refuse exactly where a
            -- factor does.
            simp only [listMeetRow] at h
            split at h
            · next hdom =>
                obtain ⟨fs, hfs⟩ :=
                  rowOfG_total (pre := fpre) (suf := fsuf) (c := f)
                    (n := max fpre.length pre₂.length + max fsuf.length suf₂.length) (by omega)
                obtain ⟨us, hus⟩ :=
                  rowOfG_total (pre := pre₂) (suf := suf₂) (c := c)
                    (n := max fpre.length pre₂.length + max fsuf.length suf₂.length) (by omega)
                rw [hfs, hus] at h
                cases hfc : f c with
                | none => rw [hfc] at h; exact absurd h (by simp)
                | some spz =>
                    rw [hfc] at h
                    obtain ⟨row, hrow, rfl⟩ := Option.map_eq_some_iff.mp h
                    have hfsl : fs.length
                        = max fpre.length pre₂.length + max fsuf.length suf₂.length :=
                      rowOfG_length hfs
                    have husl : us.length
                        = max fpre.length pre₂.length + max fsuf.length suf₂.length :=
                      rowOfG_length hus
                    have hFz : List.Forall₂
                        (fun (p : (Term → Option Term) × Term) w => p.1 p.2 = some w)
                        (fs.zip us) row :=
                      allSome_map_forall₂ _ (by rw [← zipF_eq]; exact hrow)
                    have hrowlen : row.length
                        = max fpre.length pre₂.length + max fsuf.length suf₂.length := by
                      have hz := hFz.length_eq
                      simp only [List.length_zip, hfsl, husl] at hz
                      omega
                    have htk : (row.take (max fpre.length pre₂.length)).length
                        = max fpre.length pre₂.length := by
                      rw [List.length_take, hrowlen]; omega
                    have hdp : (row.drop (max fpre.length pre₂.length)).length
                        = max fsuf.length suf₂.length := by
                      rw [List.length_drop, hrowlen]; omega
                    obtain ⟨ts, hts, htsF⟩ :=
                      rowOfG_forall₂_left hp (Or.inr ⟨t, f, rfl, rfl, hsound⟩) hf hfs
                    have htsl : ts.length
                        = max fpre.length pre₂.length + max fsuf.length suf₂.length :=
                      rowOfG_length hts
                    have hrel₀ := zipF_lift_terms htsF hFz
                    have hspz : ∀ u, Adm spz u = (Adm t u && Adm c u) := hsound c spz hfc
                    have hdm := dominates_max hdom
                    rw [Adm_listOf]
                    refine Adm_list_rows (p₁ := pre) (q₁ := some t) (s₁ := suf) ?_ ?_ v
                    · intro n
                      simp only [rowOfG_some_isSome, htk, hdp]
                      rcases Nat.lt_or_ge n (pre.length + suf.length) with h1 | h1
                      · rw [decide_eq_false (by omega : ¬ (max fpre.length pre₂.length
                          + max fsuf.length suf₂.length ≤ n)),
                          decide_eq_false (by omega : ¬ (pre.length + suf.length ≤ n)),
                          Bool.false_and]
                      · rcases Nat.lt_or_ge n (pre₂.length + suf₂.length) with h2 | h2
                        · rw [decide_eq_false (by omega : ¬ (max fpre.length pre₂.length
                            + max fsuf.length suf₂.length ≤ n)),
                            decide_eq_true (by omega : pre.length + suf.length ≤ n),
                            decide_eq_false (by omega : ¬ (pre₂.length + suf₂.length ≤ n)),
                            Bool.and_false]
                        · rw [decide_eq_true (by omega : max fpre.length pre₂.length
                            + max fsuf.length suf₂.length ≤ n),
                            decide_eq_true (by omega : pre.length + suf.length ≤ n),
                            decide_eq_true (by omega : pre₂.length + suf₂.length ≤ n),
                            Bool.and_self]
                    · intro n r₁ r₂ rz h1 h2 h3
                      rw [rowOfG_some_eq, htk, hdp] at h3
                      split at h3
                      · exact absurd h3 (by simp)
                      · next hge =>
                          simp only [Option.some.injEq] at h3
                          subst h3
                          have hr₁ := rowOfG_respread (P := max fpre.length pre₂.length)
                            (S := max fsuf.length suf₂.length)
                            (by omega) (by omega) (by omega) hts h1
                          have hr₂ := rowOfG_respread (P := max fpre.length pre₂.length)
                            (S := max fsuf.length suf₂.length)
                            (by omega) (by omega) (by omega) hus h2
                          subst hr₁; subst hr₂
                          refine ⟨?_, ?_⟩
                          · simp only [List.length_append, List.length_take, List.length_drop,
                              List.length_replicate, htsl, husl]
                          · refine forall₂_zip_append ?_
                              (forall₂_zip_append ?_ (forall₂_zip_take _ hrel₀)
                                (forall₂_zip_replicate hspz _))
                              (forall₂_zip_drop _ hrel₀)
                            · simp only [List.length_append, List.length_take,
                                List.length_replicate, htsl, husl]
                            · simp only [List.length_take, htsl, husl]
            · exact absurd h (by simp)
  case opaq => simp [famList] at h
  all_goals fam_never famList

/-! ### The object families. A body is read as its slot at every name, so each factor and the
     meet are stated through one function. -/

/-- **The slot a body gives one name**: the declared slot, or `optional` of the block. A body
    is a total function from the key space to a slot, and this is that function. -/
def Body.slotAt (b : Body) (k : Name) : ObjectSlot :=
  if h : k ∈ b.fields then b.at ⟨k, h⟩ else .optional b.block

/-- A declared name's slot is the declared one. -/
theorem Body.slotAt_pos {b : Body} {k : Name} (h : k ∈ b.fields) : b.slotAt k = b.at ⟨k, h⟩ := by
  unfold Body.slotAt; rw [dif_pos h]

/-- An undeclared name's slot is `optional` of the block. -/
theorem Body.slotAt_neg {b : Body} {k : Name} (h : k ∉ b.fields) : b.slotAt k = .optional b.block := by
  unfold Body.slotAt; rw [dif_neg h]

/-- **A term's slot at one name**, where the term is an object. The vector bridge states an
    object answer through this, because two bodies are one body exactly when their slots agree
    at every name and their blocks agree. -/
def Term.slotAt : Term → Name → Option ObjectSlot
  | .object b, k => some (b.slotAt k)
  | _, _ => none

/-- **A term's option at one position**: a union's option there, and a term that is not a union
    as its own single option. The bridge states a union of object answers option by option. -/
def Term.optionAt : Term → Nat → Option Term
  | .union os, i => os[i]?
  | t, 0 => some t
  | _, _ + 1 => none

/-- A term's open block, where the term is an object: `none` inside for a closed body. -/
def Term.blockOf : Term → Option (Option Term)
  | .object b => some b.wild
  | _ => none

/-- The required names, read over the whole key space: an undeclared name is `optional`. -/
theorem reqs_slotAt (c : Body) (keys : Finset Name) :
    decide (∀ k : {k // k ∈ c.fields}, ObjectSlot.isReq (c.at k) = true → k.1 ∈ keys) = true ↔
    ∀ k, ObjectSlot.isReq (c.slotAt k) = true → k ∈ keys := by
  rw [decide_eq_true_iff]
  constructor
  · intro h k hr
    rcases Decidable.em (k ∈ c.fields) with hk | hk
    · rw [Body.slotAt_pos hk] at hr; exact h ⟨k, hk⟩ hr
    · rw [Body.slotAt_neg hk] at hr; exact absurd hr (by simp [ObjectSlot.isReq])
  · intro h k hr; exact h k.1 (by rw [Body.slotAt_pos k.2]; exact hr)

/-- **A body admits a map by its slots**: every name whose slot is required is present, and
    every present name passes its slot. -/
theorem AdmBody_map_slots (c : Body) (keys : Finset Name) (g : {k // k ∈ keys} → Value) :
    AdmBody c (.map keys g) = true ↔
      (∀ k, ObjectSlot.isReq (c.slotAt k) = true → k ∈ keys) ∧
      ∀ k : {k // k ∈ keys}, AdmField (c.slotAt k.1) (g k) = true := by
  rw [AdmBody_map, valPresentT_req, Bool.and_eq_true, reqs_slotAt]
  apply and_congr Iff.rfl
  unfold objAdmV; rw [decide_eq_true_iff]
  refine forall_congr' fun k => ?_
  unfold entryP; simp only [MapOf.at]
  rcases Decidable.em (k.1 ∈ c.fields) with hk | hk
  · rw [dif_pos hk, Body.slotAt_pos hk]
  · rw [dif_neg hk, Body.slotAt_neg hk]
    cases hw : c.wild with
    | none => simp [AdmWild, Body.block, hw, AdmField, Adm]
    | some t => simp [AdmWild, Body.block, hw, AdmField]

/-- **Two bodies conjoined at every name are conjoined as bodies.** -/
theorem AdmBody_of_slots {a b z : Body}
    (hS : ∀ k w, AdmField (z.slotAt k) w = (AdmField (a.slotAt k) w && AdmField (b.slotAt k) w))
    (hR : ∀ k, ObjectSlot.isReq (z.slotAt k)
      = (ObjectSlot.isReq (a.slotAt k) || ObjectSlot.isReq (b.slotAt k)))
    (v : Value) : AdmBody z v = (AdmBody a v && AdmBody b v) := by
  cases v
  case map keys g =>
    rw [Bool.eq_iff_iff, Bool.and_eq_true, AdmBody_map_slots, AdmBody_map_slots,
      AdmBody_map_slots]
    constructor
    · rintro ⟨hr, hs⟩
      refine ⟨⟨fun k h => hr k (by rw [hR, h, Bool.true_or]), fun k => ?_⟩,
        ⟨fun k h => hr k (by rw [hR, h, Bool.or_true]), fun k => ?_⟩⟩
      · have h1 := hs k; rw [hS, Bool.and_eq_true] at h1; exact h1.1
      · have h1 := hs k; rw [hS, Bool.and_eq_true] at h1; exact h1.2
    · rintro ⟨⟨hra, hsa⟩, ⟨hrb, hsb⟩⟩
      refine ⟨fun k h => ?_, fun k => by rw [hS, hsa k, hsb k]; rfl⟩
      rw [hR, Bool.or_eq_true] at h
      exact h.elim (hra k) (hrb k)
  all_goals
    rw [AdmBody_of_not_map (fun _ _ hc => Value.noConfusion hc),
      AdmBody_of_not_map (fun _ _ hc => Value.noConfusion hc),
      AdmBody_of_not_map (fun _ _ hc => Value.noConfusion hc)]; rfl

/-- **A slot at the bottom empties the product**, at a name either body requires. -/
theorem AdmBody_false_of_bottom {a b : Body} {s : ObjectSlot} {k : Name}
    (hs : ∀ w, AdmField s w = (AdmField (a.slotAt k) w && AdmField (b.slotAt k) w))
    (hr : ObjectSlot.isReq s = (ObjectSlot.isReq (a.slotAt k) || ObjectSlot.isReq (b.slotAt k)))
    (hbot : ObjectSlot.isBottom s = true) (v : Value) :
    (AdmBody a v && AdmBody b v) = false := by
  refine Bool.eq_false_iff.mpr (fun hab => ?_)
  rw [Bool.and_eq_true] at hab
  obtain ⟨hA, hB⟩ := hab
  cases v
  case map keys g =>
    rw [AdmBody_map_slots] at hA hB
    have hreq := isReq_of_isBottom hbot
    rw [hr, Bool.or_eq_true] at hreq
    have hk : k ∈ keys := hreq.elim (hA.1 k) (hB.1 k)
    have h1 := hs (g ⟨k, hk⟩)
    rw [hA.2 ⟨k, hk⟩, hB.2 ⟨k, hk⟩] at h1
    cases s with
    | req t =>
      have ht : t = .never := by
        cases t <;> simp_all [ObjectSlot.isBottom, Term.isNever]
      subst ht; exact absurd h1 (by simp [AdmField, Adm])
    | optional t => exact absurd hbot (by simp [ObjectSlot.isBottom])
  all_goals exact absurd hA (by rw [AdmBody_of_not_map (fun _ _ hc => Value.noConfusion hc)]; simp)

/-- The presence test reads the marks alone, so a field table with the body's marks has the
    body's test. -/
theorem valPresentT_of_isReq {b : Body} {F : {k // k ∈ b.fields} → ObjectSlot}
    (hreq : ∀ k, ObjectSlot.isReq (F k) = ObjectSlot.isReq (b.at k)) (keys : Finset Name) :
    valPresentT b.fields F keys = valPresentT b.fields b.at keys := by
  rw [valPresentT_req, valPresentT_req]
  exact decide_eq_decide.mpr (forall_congr' fun k => by rw [hreq k])

/-- Every present name goes through its field and the left operand's term alike. -/
theorem objAdmV_of_left {b : Body} {x t r : Term} {F : {k // k ∈ b.fields} → ObjectSlot}
    (ihf : ∀ (k : {k // k ∈ b.fields}) (w : Value),
      AdmField (F k) w = (Adm x w && AdmField (b.at k) w))
    (iht : ∀ w, Adm r w = (Adm x w && Adm t w))
    (keys : Finset Name) (g : {k // k ∈ keys} → Value) :
    objAdmV ⟨b.fields, fun k => AdmField (F k)⟩ (some (Adm r)) keys g
      = (decide (∀ k : {k // k ∈ keys}, Adm x (g k) = true)
         && objAdmV ⟨b.fields, fun k => AdmField (b.at k)⟩ (some (Adm t)) keys g) := by
  simp only [objAdmV, entryP, MapOf.at]
  refine decide_forall_and (fun k => ?_)
  by_cases hk : k.1 ∈ b.fields
  · simp only [dif_pos hk]; exact ihf ⟨k.1, hk⟩ (g k)
  · simp only [dif_neg hk]; exact iht (g k)

/-- No declared field meets the left operand's term to the bottom at a value both admit. -/
theorem isBottom_false_of_left {b : Body} {x : Term} {F : {k // k ∈ b.fields} → ObjectSlot}
    (hreq : ∀ k, ObjectSlot.isReq (F k) = ObjectSlot.isReq (b.at k))
    (ihf : ∀ (k : {k // k ∈ b.fields}) (w : Value),
      AdmField (F k) w = (Adm x w && AdmField (b.at k) w))
    {keys : Finset Name} {g : {k // k ∈ keys} → Value}
    (hA : AdmBody b (.map keys g) = true)
    (hR : decide (∀ k : {k // k ∈ keys}, Adm x (g k) = true) = true) :
    ∀ k, ObjectSlot.isBottom (F k) = false := by
  rw [AdmBody_map, Bool.and_eq_true] at hA
  intro k
  refine Bool.eq_false_iff.mpr (fun hbot => ?_)
  have hreqk : ObjectSlot.isReq (b.at k) = true := (hreq k) ▸ isReq_of_isBottom hbot
  have hk : k.1 ∈ keys := mem_keys_of_isReq hA.1 k.2 hreqk
  have hrow := objAdmV_row hA.2 hk k.2
  have hrec := of_decide_eq_true hR ⟨k.1, hk⟩
  have hi := ihf k (g ⟨k.1, hk⟩)
  rw [AdmField_of_isBottom hbot, hrow, hrec] at hi
  exact absurd hi (by simp)

/-! ### Two bodies, met pointwise -/

/-- **One name of the met body, on the write side**: the slot the meet gives a name admits
    exactly what both bodies' slots at that name admit, and is required where either is. -/
theorem objSlot_sound {a b : Body} {g : {k // k ∈ a.fields} → ObjectSlot → Option ObjectSlot}
    {mw : Term → Option Term}
    (hg : ∀ (k : {k // k ∈ a.fields}) (fl fm : ObjectSlot), g k fl = some fm →
      ∀ w, AdmField fm w = (AdmField (a.at k) w && AdmField fl w))
    (hgreq : ∀ (k : {k // k ∈ a.fields}) (fl fm : ObjectSlot), g k fl = some fm →
      ObjectSlot.isReq fm = (ObjectSlot.isReq (a.at k) || ObjectSlot.isReq fl))
    (hw : ∀ y z, mw y = some z → ∀ w, Adm z w = (Adm a.block w && Adm y w))
    {k : {k // k ∈ a.fields ∪ b.fields}} {s : ObjectSlot} (h : objSlot a b g mw k = some s) :
    (∀ w, AdmField s w = (AdmField (a.slotAt k.1) w && AdmField (b.slotAt k.1) w)) ∧
    ObjectSlot.isReq s = (ObjectSlot.isReq (a.slotAt k.1) || ObjectSlot.isReq (b.slotAt k.1)) := by
  unfold objSlot at h
  split at h
  next ha =>
    have hb : (if h' : k.1 ∈ b.fields then b.at ⟨k.1, h'⟩ else .optional b.block)
        = b.slotAt k.1 := rfl
    rw [hb] at h
    rw [Body.slotAt_pos ha]
    exact ⟨hg _ _ _ h, hgreq _ _ _ h⟩
  next ha =>
    have hb := (Finset.mem_union.mp k.2).resolve_left ha
    rw [Body.slotAt_neg ha, Body.slotAt_pos hb]
    cases hf : b.at ⟨k.1, hb⟩ with
    | req y =>
      rw [hf] at h
      simp only [ObjectSlot.through, Option.map_eq_some_iff] at h
      obtain ⟨z, hz, rfl⟩ := h
      exact ⟨fun w => hw _ _ hz w, rfl⟩
    | optional y =>
      rw [hf] at h
      simp only [ObjectSlot.through, Option.map_eq_some_iff] at h
      obtain ⟨z, hz, rfl⟩ := h
      exact ⟨fun w => hw _ _ hz w, rfl⟩

/-- **The met body's slot at every name**, from the slots at the names of either body and
    the block at the rest. A name the normal form drops states the default `never`. -/
theorem objObj_slots {a b : Body} {g : {k // k ∈ a.fields} → ObjectSlot → Option ObjectSlot}
    {mw : Term → Option Term} {zb : Term} {P : Name → ObjectSlot → Prop}
    (hall : ∀ k : {k // k ∈ a.fields ∪ b.fields}, (objSlot a b g mw k).isSome = true)
    (hslot : ∀ (k : {k // k ∈ a.fields ∪ b.fields}) s, objSlot a b g mw k = some s → P k.1 s)
    (hblk : ∀ k, k ∉ a.fields → k ∉ b.fields →
      P k (.optional (if zb.isNever then .never else zb)))
    (k : Name) :
    P k (Body.slotAt (.mk ((a.fields ∪ b.fields).filter (fun k =>
          (if h : k ∈ a.fields ∪ b.fields then
            !(zb.isNever && ObjectSlot.isAbsentOpt (objSlot a b g mw ⟨k, h⟩))
          else false) = true))
        (fun k => (objSlot a b g mw ⟨k.1, (Finset.mem_filter.mp k.2).1⟩).getD (.optional .never))
        (if zb.isNever then none else some zb)) k) := by
  have hblock : Body.block (.mk ((a.fields ∪ b.fields).filter (fun k =>
          (if h : k ∈ a.fields ∪ b.fields then
            !(zb.isNever && ObjectSlot.isAbsentOpt (objSlot a b g mw ⟨k, h⟩))
          else false) = true))
        (fun k => (objSlot a b g mw ⟨k.1, (Finset.mem_filter.mp k.2).1⟩).getD (.optional .never))
        (if zb.isNever then none else some zb)) = (if zb.isNever then .never else zb) := by
    cases zb.isNever <;> rfl
  rcases Decidable.em (k ∈ (a.fields ∪ b.fields).filter (fun k =>
      (if h : k ∈ a.fields ∪ b.fields then
        !(zb.isNever && ObjectSlot.isAbsentOpt (objSlot a b g mw ⟨k, h⟩))
      else false) = true)) with hk | hk
  · rw [Body.slotAt_pos hk]
    simp only [Body.at_mk]
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (hall ⟨k, (Finset.mem_filter.mp hk).1⟩)
    rw [hs, Option.getD_some]
    exact hslot _ s hs
  · rw [Body.slotAt_neg hk, hblock]
    rcases Decidable.em (k ∈ a.fields ∪ b.fields) with hU | hU
    · have hkeep : (!(zb.isNever && ObjectSlot.isAbsentOpt (objSlot a b g mw ⟨k, hU⟩))) = false := by
        refine Bool.eq_false_iff.mpr (fun ht => hk (Finset.mem_filter.mpr ⟨hU, ?_⟩))
        rw [dif_pos hU]; exact ht
      rw [Bool.not_eq_false', Bool.and_eq_true] at hkeep
      obtain ⟨hnev, habs⟩ := hkeep
      obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (hall ⟨k, hU⟩)
      rw [hs] at habs
      cases s with
      | req t => exact absurd habs (by simp [ObjectSlot.isAbsentOpt])
      | optional t =>
        have ht : t = .never := by
          cases t <;> simp_all [ObjectSlot.isAbsentOpt, Term.isNever]
        subst ht
        rw [hnev, if_pos rfl]
        exact hslot _ _ hs
    · have ha : k ∉ a.fields := fun h => hU (Finset.mem_union.mpr (Or.inl h))
      have hb : k ∉ b.fields := fun h => hU (Finset.mem_union.mpr (Or.inr h))
      exact hblk k ha hb

/-- **Two objects meet pointwise, and the meet is exact on the write side.** -/
theorem Adm_famObj {a : Body} {g : {k // k ∈ a.fields} → ObjectSlot → Option ObjectSlot}
    {mw : Term → Option Term}
    (hg : ∀ (k : {k // k ∈ a.fields}) (fl fm : ObjectSlot), g k fl = some fm →
      ∀ w, AdmField fm w = (AdmField (a.at k) w && AdmField fl w))
    (hgreq : ∀ (k : {k // k ∈ a.fields}) (fl fm : ObjectSlot), g k fl = some fm →
      ObjectSlot.isReq fm = (ObjectSlot.isReq (a.at k) || ObjectSlot.isReq fl))
    (hw : ∀ y z, mw y = some z → ∀ w, Adm z w = (Adm a.block w && Adm y w)) :
    AdmFam (.object a) (famObj a g mw) := by
  intro y z hd h v
  cases y <;> first | exact hd.elim | skip
  case object b =>
      simp only [famObj] at h
      unfold objObj at h
      split at h
      next hbot =>
        obtain ⟨k, hk⟩ := of_decide_eq_true hbot
        obtain ⟨s, hs, hsb⟩ := Option.map_eq_some_iff.mp hk
        simp only [Option.some.injEq] at h; subst h
        obtain ⟨hS, hR⟩ := objSlot_sound hg hgreq hw hs
        exact (AdmBody_false_of_bottom hS hR hsb v).symm
      next =>
        split at h
        next => exact absurd h (by simp)
        next zb hwz =>
          split at h
          next hall =>
            simp only [Option.some.injEq] at h; subst h
            have hblkA : ∀ w, Adm (if zb.isNever then .never else zb) w
                = (Adm a.block w && Adm b.block w) := by
              intro w
              cases hn : zb.isNever
              · exact hw _ _ hwz w
              · rw [if_pos rfl, ← hw _ _ hwz w, eq_never_of_isNever hn]
            refine AdmBody_of_slots (fun k w => ?_) (fun k => ?_) v
            · exact objObj_slots (P := fun k s => AdmField s w
                  = (AdmField (a.slotAt k) w && AdmField (b.slotAt k) w))
                (of_decide_eq_true hall) (fun k' s hs => (objSlot_sound hg hgreq hw hs).1 w)
                (fun k' ha hb => by
                  rw [Body.slotAt_neg ha, Body.slotAt_neg hb]; exact hblkA w) k
            · exact objObj_slots (P := fun k s => ObjectSlot.isReq s
                  = (ObjectSlot.isReq (a.slotAt k) || ObjectSlot.isReq (b.slotAt k)))
                (of_decide_eq_true hall) (fun k' s hs => (objSlot_sound hg hgreq hw hs).2)
                (fun k' ha hb => by rw [Body.slotAt_neg ha, Body.slotAt_neg hb]; rfl) k
          next => exact absurd h (by simp)
  case opaq => simp [famObj] at h
  all_goals fam_never famObj

/-! ### The outer theorem. -/

/-- Two fields meet at the stronger mark, so the write bit is the join. -/
theorem isReq_Field_meet : ∀ {f fl fm : ObjectSlot}, ObjectSlot.meet f fl = some fm →
    ObjectSlot.isReq fm = (ObjectSlot.isReq f || ObjectSlot.isReq fl) := by
  intro f fl fm h
  match f, fl, h with
  | .req _, .req _, h
  | .req _, .optional _, h
  | .optional _, .req _, h
  | .optional _, .optional _, h =>
      simp only [ObjectSlot.meet, Option.map_eq_some_iff] at h
      obtain ⟨tz, _, rfl⟩ := h
      rfl

/-- The option companion is the plain map at the fixed partner. -/
theorem meetSL_eq (y : Term) : ∀ os, Term.meetSL os y = os.map (fun t => Term.meet t y)
  | [] => rfl
  | _ :: os => congrArg _ (meetSL_eq y os)

/-- A certified union distributes: every option meets, the bottoms drop, and the survivors
    carry the certificate. -/
theorem meet_union_of {os : List Term} {y z : Term}
    (h : Term.meet (.union os) y = some z) (hy : y ≠ .never) :
    ∃ zs, List.Forall₂ (fun t w => Term.meet t y = some w) os zs ∧
      z = Term.ofOptions (zs.filter (fun w => !w.isNever)) := by
  rw [Term.meet] at h
  · obtain ⟨zs, hzs, hg⟩ := Option.bind_eq_some_iff.mp h
    refine ⟨zs, allSome_map_forall₂ _ ?_, (Option.some.inj hg).symm⟩
    rw [← meetSL_eq]
    exact hzs
  all_goals (intros; simp_all)

mutual
/-- **`Adm` is a homomorphism from the meet to conjunction.** Where two terms have a meet,
    the values it admits are exactly the values both admit. -/
theorem Adm_meet : ∀ x y z, Term.meet x y = some z → ∀ v, Adm z v = (Adm x v && Adm y v)
  | .never, _, _, h, _ => by
      simp only [Term.meet, Option.some.injEq] at h; subst h; simp [Adm]
  | .held _ _ _ _, y, _, h, v => by
      cases y <;>
        first
          | (simp only [Term.meet, Option.some.injEq] at h; subst h; simp [Adm])
          | exact absurd h (by simp [Term.meet])
  | .lazy x, y, _, h, v => by
      rw [Term.meet] at h
      simpa [Adm] using Adm_meet x y _ h v
  | .refine x p, y, _, h, v => by
      cases y with
      | never =>
          simp only [Term.meet, Option.some.injEq] at h; subst h; simp [Adm]
      | _ =>
        simp only [Term.meet] at h
        split at h
        · obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
          have ihw := Adm_meet x _ w hw v
          rw [Adm_refineOf]
          simp only [Adm, ihw]
          simp [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]
        · exact absurd h (by simp)
  | .union os, y, _, h, v => by
      cases y with
      | never =>
          simp only [Term.meet, Option.some.injEq] at h; subst h; simp [Adm]
      | _ =>
        obtain ⟨zs, hF, rfl⟩ := meet_union_of h (by simp)
        exact union_meet_free v (Adm_meetL os _ _ hF)
  | .string, y, z, h, v => Adm_meetSRight Adm_famString y z h v
  | .number, y, z, h, v => Adm_meetSRight Adm_famNumber y z h v
  | .boolean, y, z, h, v => Adm_meetSRight Adm_famBoolean y z h v
  | .binary, y, z, h, v => Adm_meetSRight Adm_famBinary y z h v
  | .null, y, z, h, v => Adm_meetSRight Adm_famNull y z h v
  | .literal k lv, y, z, h, v => Adm_meetSRight (Adm_famLit k lv) y z h v
  | .set b, y, z, h, v => Adm_meetSRight (Adm_famSet b) y z h v
  | .opaq, y, z, h, v => Adm_meetSRight (Adm_famOpaq) y z h v
  | .list pre sp suf, y, z, h, v => by
      cases sp with
      | none =>
          exact Adm_meetSRight (Adm_famList (pre := pre) (sp := none) (suf := suf)
            (Adm_meetSTs pre) (Or.inl ⟨rfl, rfl⟩) (Adm_meetSTs suf)) y z h v
      | some t =>
          exact Adm_meetSRight (Adm_famList (pre := pre) (sp := some t) (suf := suf)
            (Adm_meetSTs pre)
            (Or.inr ⟨t, Term.meet t, rfl, rfl, fun u w hw => Adm_meet t u w hw⟩)
            (Adm_meetSTs suf)) y z h v
  | .object (.mk fs f none), y, z, h, v =>
      Adm_meetSRight (Adm_famObj (a := .mk fs f none)
        (fun k fl fm hm w => Adm_Field_meet (f k) fl fm hm w)
        (fun _ _ _ hm => isReq_Field_meet hm)
        (fun _ _ hz _ => by simp only [Option.some.injEq] at hz; subst hz; rfl)) y z h v
  | .object (.mk fs f (some t)), y, z, h, v =>
      Adm_meetSRight (Adm_famObj (a := .mk fs f (some t))
        (fun k fl fm hm w => Adm_Field_meet (f k) fl fm hm w)
        (fun _ _ _ hm => isReq_Field_meet hm)
        (fun u w hw => Adm_meet t u w hw)) y z h v
termination_by structural x => x

/-- The union row's options, lifted pointwise at the fixed partner. -/
theorem Adm_meetL : ∀ (os : List Term) (y : Term) (zs : List Term),
    List.Forall₂ (fun t w => Term.meet t y = some w) os zs →
    List.Forall₂ (fun t w => ∀ u, Adm w u = (Adm t u && Adm y u)) os zs
  | [], _, _, h => by cases h; exact .nil
  | t :: ts, y, _, h => by
      cases h with
      | cons hh ht => exact .cons (fun u => Adm_meet t y _ hh u) (Adm_meetL ts y _ ht)
termination_by structural os => os

/-- Every position of a tuple carries the meet at that position. -/
theorem Adm_meetSTs : ∀ ts : List Term, List.Forall₂ AdmSound ts (Term.meetSTs ts)
  | [] => .nil
  | t :: ts => .cons (fun u w hw => Adm_meet t u w hw) (Adm_meetSTs ts)
termination_by structural ts => ts

/-- Two fields at one name admit what both admit, at the stronger mark. -/
theorem Adm_Field_meet : ∀ (f fl : ObjectSlot) (fm : ObjectSlot), ObjectSlot.meet f fl = some fm →
    ∀ w, AdmField fm w = (AdmField f w && AdmField fl w)
  | .req x, .req y, _, h, w => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact Adm_meet x y tz hz w
  | .req x, .optional y, _, h, w => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact Adm_meet x y tz hz w
  | .optional x, .req y, _, h, w => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact Adm_meet x y tz hz w
  | .optional x, .optional y, _, h, w => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact Adm_meet x y tz hz w
termination_by structural f => f
end

end StructuralAdm

/-- A unanimous list names one member, so every entry is that member. -/
theorem unanimous_all : ∀ {μs : List (Option Member)} {m : Member},
    unanimous μs = some m → ∀ u ∈ μs, u = some m
  | [], _, h => by simp [unanimous] at h
  | μ :: μs, m, h => by
      simp only [unanimous] at h
      split at h
      next hall =>
        subst h
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu'
        · rfl
        · exact of_decide_eq_true (by simpa using (List.all_eq_true.mp hall) u hu')
      next => exact absurd h (by simp)

/-- An option's member is one of the list's. -/
theorem mem_μSynList : ∀ {os : List Term} {o : Term}, o ∈ os → μSyn o ∈ μSynList os
  | [], _, h => by simp at h
  | t :: ts, o, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_μSynList h')

/-- Every option of a union that names a member names that one. -/
theorem μSyn_union_mem {os : List Term} {m : Member} (h : μSyn (.union os) = some m) :
    ∀ o ∈ os, μSyn o = some m := by
  intro o ho
  exact unanimous_all (by simpa only [μSyn] using h) _ (mem_μSynList ho)

/-- …and a list of survivors that names a member has one that does. -/
theorem μSyn_ofOptions_mem {ts : List Term} {m : Member}
    (h : μSyn (Term.ofOptions ts) = some m) : ∃ t ∈ ts, μSyn t = some m := by
  match ts with
  | [] => exact absurd h (by simp [Term.ofOptions, μSyn])
  | [t] => exact ⟨t, by simp, h⟩
  | a :: b :: rest =>
      exact ⟨a, by simp, μSyn_union_mem (os := a :: b :: rest) h a (by simp)⟩


section StructuralWrites
set_option maxHeartbeats 1000000

/-! ## The member the meet names, structurally

The same three layers the homomorphism uses. The containers never read the recursion here:
`μSyn` of an `array`, a `tuple`, a `record` and an `object` is fixed by the constructor whatever
the payload meets to, so only the refinement and the union rows recurse. -/

/-- `fam` carries the member with one term fixed on the left, over the operands it is handed. -/
def WritesFam (x : Term) (fam : Term → Option Term) : Prop :=
  ∀ y z, Delegated y → fam y = some z → ∀ m : Member, μSyn z = some m →
    (∀ mx, μSyn x = some mx → mx = m) ∧ (∀ my, μSyn y = some my → my = m)

mutual
/-- Every row that reads the right operand alone names the family's member. -/
theorem writes_meetSRight {x : Term} {fam : Term → Option Term} (hf : WritesFam x fam) :
    ∀ y z, meetSRight fam y = some z → ∀ m : Member, μSyn z = some m →
      (∀ mx, μSyn x = some mx → mx = m) ∧ (∀ my, μSyn y = some my → my = m)
  | .never, _, h, _, hz => by
      simp only [meetSRight, Option.some.injEq] at h; subst h
      exact absurd hz (by simp [μSyn])
  | .held _ _ _ _, _, h, _, _ => by simp [meetSRight] at h
  | .lazy t, _, h, m, hz => by
      rw [meetSRight] at h
      refine ⟨(writes_meetSRight hf t _ h m hz).1, ?_⟩
      intro my hmy; exact absurd hmy (by simp [μSyn])
  | .refine y p, _, h, m, hz => by
      simp only [meetSRight] at h
      split at h
      · obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
        replace hz := μSyn_refineOf hz
        have ih := writes_meetSRight hf y w hw m hz
        exact ⟨ih.1, fun my hmy => ih.2 my (by simpa [μSyn] using hmy)⟩
      · exact absurd h (by simp)
  | .union os, _, h, m, hz => by
      obtain ⟨zs, hF, _, _, rfl⟩ := meetSRight_union h
      obtain ⟨w, hw, hwm⟩ := μSyn_ofOptions_mem hz
      obtain ⟨o, ho, hP⟩ :=
        forall₂_mem_right (writes_meetSRightL hf os zs hF) (List.mem_of_mem_filter hw)
      have ih := hP m hwm
      exact ⟨ih.1, fun my hmy => ih.2 my (μSyn_union_mem hmy o ho)⟩
  | .string, _, h, m, hz => hf .string _ trivial h m hz
  | .number, _, h, m, hz => hf .number _ trivial h m hz
  | .boolean, _, h, m, hz => hf .boolean _ trivial h m hz
  | .binary, _, h, m, hz => hf .binary _ trivial h m hz
  | .null, _, h, m, hz => hf .null _ trivial h m hz
  | .literal k lv, _, h, m, hz => hf (.literal k lv) _ trivial h m hz
  | .set b, _, h, m, hz => hf (.set b) _ trivial h m hz
  | .opaq, _, h, m, hz => hf .opaq _ trivial h m hz
  | .list p q s, _, h, m, hz => hf (.list p q s) _ trivial h m hz
  | .object b, _, h, m, hz => hf (.object b) _ trivial h m hz
termination_by structural y => y

/-- The union row's options, lifted pointwise. -/
theorem writes_meetSRightL {x : Term} {fam : Term → Option Term} (hf : WritesFam x fam) :
    ∀ os zs, List.Forall₂ (fun t w => meetSRight fam t = some w) os zs →
      List.Forall₂ (fun t w => ∀ m : Member, μSyn w = some m →
        (∀ mx, μSyn x = some mx → mx = m) ∧ (∀ my, μSyn t = some my → my = m)) os zs
  | [], _, h => by cases h; exact .nil
  | t :: ts, _, h => by
      cases h with
      | cons hh ht =>
          exact .cons (fun m hm => writes_meetSRight hf t _ hh m hm)
            (writes_meetSRightL hf ts _ ht)
termination_by structural os => os
end

/-- `string` names `S`, and so does every term it meets. -/
theorem writes_famString : WritesFam Term.string famString := by
  intro y z hd h m hz
  cases y <;> first | exact hd.elim | skip
  case literal k lv =>
      cases k <;> (try simp_all [famString, μSyn]) <;>
        (try (subst_vars; simp_all [μSyn, GroundKind.member]))
      all_goals (try (split at h))
      all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
      all_goals (try (subst h; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars; simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz; exact hz.symm))
  all_goals (try simp_all [famString, μSyn, Term.meetLit])
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars
                  simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz
                  exact ⟨fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member], fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member]⟩))
  all_goals (try (subst h; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars; simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz; exact hz.symm))

/-- `number` names `N`, and so does every term it meets. -/
theorem writes_famNumber : WritesFam Term.number famNumber := by
  intro y z hd h m hz
  cases y <;> first | exact hd.elim | skip
  case literal k lv =>
      cases k <;> (try simp_all [famNumber, μSyn, Term.meetLit]) <;>
        (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
      all_goals (try (split at h))
      all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
      all_goals (try (subst h; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars; simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz; exact hz.symm))
  all_goals (try simp_all [famNumber, μSyn, Term.meetLit])
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars
                  simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz
                  exact ⟨fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member], fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member]⟩))
  all_goals (try (subst h; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars; simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz; exact hz.symm))


/-- `boolean` names `BOOL`, and so does every term it meets. -/
theorem writes_famBoolean : WritesFam Term.boolean famBoolean := by
  intro y z hd h m hz
  cases y <;> first | exact hd.elim | skip
  case literal k lv =>
      cases k <;> (try simp_all [famBoolean, μSyn, Term.meetLit]) <;>
        (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
      all_goals (try (split at h))
      all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
      all_goals (try (subst h; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars; simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz; exact hz.symm))
  all_goals (try simp_all [famBoolean, μSyn, Term.meetLit])
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars
                  simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz
                  exact ⟨fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member], fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member]⟩))
  all_goals (try (subst h; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars; simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz; exact hz.symm))

/-- `binary` names `B`, and so does every term it meets. -/
theorem writes_famBinary : WritesFam Term.binary famBinary := by
  intro y z hd h m hz
  cases y <;> first | exact hd.elim | skip
  case literal k lv =>
      cases k <;> (try simp_all [famBinary, μSyn, Term.meetLit]) <;>
        (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
      all_goals (try (split at h))
      all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
      all_goals (try (subst h; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars; simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz; exact hz.symm))
  all_goals (try simp_all [famBinary, μSyn, Term.meetLit])
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars
                  simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz
                  exact ⟨fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member], fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member]⟩))
  all_goals (try (subst h; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars; simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz; exact hz.symm))

/-- `null` names `NULL`, and so does every term it meets. -/
theorem writes_famNull : WritesFam Term.null famNull := by
  intro y z hd h m hz
  cases y <;> first | exact hd.elim | skip
  case literal k lv =>
      cases k <;> (try simp_all [famNull, μSyn, Term.meetLit]) <;>
        (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
      all_goals (try (split at h))
      all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
      all_goals (try (subst h; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars; simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz; exact hz.symm))
  all_goals (try simp_all [famNull, μSyn, Term.meetLit])
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars
                  simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz
                  exact ⟨fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member], fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member]⟩))
  all_goals (try (subst h; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars; simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz; exact hz.symm))

/-- A literal names its base's member, and so does every term it meets. -/
theorem writes_famLit (k : GroundKind) (lv : k.Carrier) :
    WritesFam (.literal k lv) (famLit k lv) := by
  intro y z hd h m hz
  cases y <;> first | exact hd.elim | skip
  case literal k' lv' =>
      cases k <;> cases k' <;> (try simp_all [famLit, μSyn, Term.meetLit, GroundKind.member])
      all_goals (try (split at h))
      all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
      all_goals (try (subst h; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars; simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz; exact hz.symm))
  all_goals (cases k <;> (try simp_all [famLit, μSyn, Term.meetLit, GroundKind.member]))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars
                  simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz
                  exact ⟨fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member], fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member]⟩))
  all_goals (try (subst h; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars; simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz; exact hz.symm))

/-- A set names its base's member, and so does every term it meets. -/
theorem writes_famSet (b : SetBase) : WritesFam (.set b) (famSet b) := by
  intro y z hd h m hz
  cases y <;> first | exact hd.elim | skip
  all_goals (cases b <;> (try simp_all [famSet, μSyn, SetBase.member]))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars
                  simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz
                  exact ⟨fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member], fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member]⟩))
  all_goals (try (subst h; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars; simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz; exact hz.symm))

/-- `opaque` names no member, so the pair agrees vacuously on the left. -/
theorem writes_famOpaq : WritesFam .opaq famOpaq := by
  intro y z hd h m hz
  cases y <;> first | exact hd.elim | skip
  all_goals (try simp_all [famOpaq, μSyn])
  all_goals (subst_vars; simp_all [μSyn])

/-- **A list names `L`, and a list it meets names `L` too.** The family answers a list or the
    bottom; the bottom writes nothing, so wherever the answer has a member that member is `L`,
    and so is each operand's. -/
theorem writes_famList {fpre : List (Term → Option Term)}
    {fsp : Option (Term → Option Term)} {fsuf : List (Term → Option Term)}
    {pre : List Term} {sp : Option Term} {suf : List Term} :
    WritesFam (.list pre sp suf) (famList fpre fsp fsuf) := by
  intro y z hd h m hz
  rcases famList_isList h with rfl | ⟨p, q, s, rfl⟩
  · exact absurd hz (by simp [μSyn])
  · simp only [μSyn, Option.some.injEq] at hz
    subst hz
    refine ⟨fun mx hmx => ?_, fun my hmy => ?_⟩
    · simp only [μSyn, Option.some.injEq] at hmx; exact hmx.symm
    · cases y <;> simp only [famList] at h <;>
        first
          | (simp only [μSyn, Option.some.injEq] at hmy; exact hmy.symm)
          | exact absurd h (by simp)

/-- Two objects meet at the bottom or at an object. -/
theorem objObj_cases {a b : Body} {g : {k // k ∈ a.fields} → ObjectSlot → Option ObjectSlot}
    {mw : Term → Option Term} {z : Term} (h : objObj a g mw b = some z) :
    z = .never ∨ ∃ c, z = .object c := by
  unfold objObj at h
  split at h
  · exact Or.inl (Option.some.inj h).symm
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact Or.inr ⟨_, (Option.some.inj h).symm⟩
      · exact absurd h (by simp)

/-- An object names `M`, and the bottom it can answer names none. -/
theorem writes_famObj {a : Body} {g : {k // k ∈ a.fields} → ObjectSlot → Option ObjectSlot}
    {mw : Term → Option Term} :
    WritesFam (.object a) (famObj a g mw) := by
  intro y z hd h m hz
  cases y <;> first | exact hd.elim | skip
  case object b =>
      rcases objObj_cases (by simpa [famObj] using h) with rfl | ⟨c, rfl⟩
      · exact absurd hz (by simp [μSyn])
      · simpa [μSyn] using hz
  all_goals (try simp_all [famObj, μSyn])
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (split at h))
  all_goals (try (subst_vars; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars
                  simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz
                  exact ⟨fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member], fun _ hh => by simp_all [μSyn, GroundKind.member, SetBase.member]⟩))
  all_goals (try (subst h; simp_all [μSyn, GroundKind.member, SetBase.member]))
  all_goals (try (subst_vars; simp only [μSyn, GroundKind.member, SetBase.member, Option.some.injEq] at hz; exact hz.symm))


mutual
/-- **Where the meet names a member, any member a factor names is that one.** `μSyn z` is a
    hypothesis and not a conclusion, because the converse fails twice: a bottom names no member,
    so two factors naming different members meet at a term that names none, and a refinement over
    the bottom is not the bottom, so excluding `never` does not repair it. -/
theorem meet_writes : ∀ x y z, Term.meet x y = some z → ∀ m : Member, μSyn z = some m →
    (∀ mx, μSyn x = some mx → mx = m) ∧ (∀ my, μSyn y = some my → my = m)
  | .never, _, _, h, _, hz => by
      simp only [Term.meet, Option.some.injEq] at h; subst h
      exact absurd hz (by simp [μSyn])
  | .held _ _ _ _, y, _, h, _, hz => by
      cases y <;>
        first
          | (simp only [Term.meet, Option.some.injEq] at h; subst h
             exact absurd hz (by simp [μSyn]))
          | exact absurd h (by simp [Term.meet])
  | .lazy x, y, _, h, m, hz => by
      rw [Term.meet] at h
      refine ⟨?_, (meet_writes x y _ h m hz).2⟩
      intro mx hmx; exact absurd hmx (by simp [μSyn])
  | .refine x p, y, _, h, m, hz => by
      cases y with
      | never =>
          simp only [Term.meet, Option.some.injEq] at h; subst h
          exact absurd hz (by simp [μSyn])
      | _ =>
        simp only [Term.meet] at h
        split at h
        · obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
          replace hz := μSyn_refineOf hz
          have ih := meet_writes x _ w hw m hz
          exact ⟨fun mx hmx => ih.1 mx (by simpa [μSyn] using hmx), ih.2⟩
        · exact absurd h (by simp)
  | .union os, y, _, h, m, hz => by
      cases y with
      | never =>
          simp only [Term.meet, Option.some.injEq] at h; subst h
          exact absurd hz (by simp [μSyn])
      | _ =>
        obtain ⟨zs, hF, _, _, rfl⟩ := meet_union_of h (by simp)
        obtain ⟨w, hw, hwm⟩ := μSyn_ofOptions_mem hz
        obtain ⟨o, ho, hP⟩ :=
          forall₂_mem_right (writes_meetL os _ zs hF) (List.mem_of_mem_filter hw)
        have ih := hP m hwm
        exact ⟨fun mx hmx => ih.1 mx (μSyn_union_mem hmx o ho), ih.2⟩
  | .string, y, z, h, m, hz => writes_meetSRight writes_famString y z h m hz
  | .number, y, z, h, m, hz => writes_meetSRight writes_famNumber y z h m hz
  | .boolean, y, z, h, m, hz => writes_meetSRight writes_famBoolean y z h m hz
  | .binary, y, z, h, m, hz => writes_meetSRight writes_famBinary y z h m hz
  | .null, y, z, h, m, hz => writes_meetSRight writes_famNull y z h m hz
  | .literal k lv, y, z, h, m, hz => writes_meetSRight (writes_famLit k lv) y z h m hz
  | .set b, y, z, h, m, hz => writes_meetSRight (writes_famSet b) y z h m hz
  | .opaq, y, z, h, m, hz => writes_meetSRight (writes_famOpaq) y z h m hz
  | .list pre sp suf, y, z, h, m, hz => by
      cases sp with
      | none =>
          exact writes_meetSRight (writes_famList (pre := pre) (sp := none) (suf := suf)
            (fpre := Term.meetSTs pre) (fsp := none)
            (fsuf := Term.meetSTs suf)) y z h m hz
      | some t =>
          exact writes_meetSRight (writes_famList (pre := pre) (sp := some t) (suf := suf)
            (fpre := Term.meetSTs pre) (fsp := some (Term.meet t))
            (fsuf := Term.meetSTs suf)) y z h m hz
  | .object (.mk fs f none), y, z, h, m, hz =>
      writes_meetSRight (writes_famObj (a := .mk fs f none)
        (g := fun k => ObjectSlot.meet (f k)) (mw := fun _ => some .never)) y z h m hz
  | .object (.mk fs f (some t)), y, z, h, m, hz =>
      writes_meetSRight (writes_famObj (a := .mk fs f (some t))
        (g := fun k => ObjectSlot.meet (f k)) (mw := Term.meet t)) y z h m hz
termination_by structural x => x

/-- The union row's options, lifted pointwise at the fixed partner. -/
theorem writes_meetL : ∀ (os : List Term) (y : Term) (zs : List Term),
    List.Forall₂ (fun t w => Term.meet t y = some w) os zs →
    List.Forall₂ (fun t w => ∀ m : Member, μSyn w = some m →
      (∀ mx, μSyn t = some mx → mx = m) ∧ (∀ my, μSyn y = some my → my = m)) os zs
  | [], _, _, h => by cases h; exact .nil
  | t :: ts, y, _, h => by
      cases h with
      | cons hh ht =>
          exact .cons (fun m hm => meet_writes t y _ hh m hm) (writes_meetL ts y _ ht)
termination_by structural os => os
end

end StructuralWrites

/-- **The converse is false, and a bottom is why.** Two factors naming different members meet at
    the bottom, which names none, so a theorem concluding `mx = my` from the factors alone fails
    here. -/
example : Term.meet (.literal .boolean true) Term.string = some .never := by rfl

example : μSyn Term.never = none := rfl

/-- The refinement that used to be the second witness is now the bottom, because the meet
    normalises: a refinement over the bottom holds nothing, so `Term.refineOf` answers the bottom.
    The hypothesis form is still the right one — the first witness needs no wrapper — and this
    example is kept because it pins the normalisation at the row that motivated it. -/
example : Term.meet (.refine .string (.members .string ⟨{"1"}, Finset.singleton_nonempty _⟩))
    .boolean = some .never := by rfl


/-! ## The homomorphism on the read side

`AdmA_meet` and `denote_meet_p` are proved together, and the pairing is forced.
`AdmA (.refine t p) a` is `AdmA t a && refineReads t p.eval a`, and `refineReads` asks the
predicate of what `t` decodes `a` to, so the refinement rows reduce to the reading agreement.
The agreement is unprovable alone: at a row that answers the bottom the meet reads nothing
where a factor reads something, and what rules that row out is the homomorphism's own content
there. The value side needs no such pairing, because `Adm (.refine t p) v` shows the predicate
the value itself.
-/


/-- A `Bool`-valued filter, compared on the set's own names. Mathlib's `Finset.filter_congr`
    reaches `Classical.choice`; a filter whose predicate is already a `Bool` needs no choice. -/
theorem filter_congr_on {S : Finset Name} {p q : Name → Bool} (h : ∀ k ∈ S, p k = q k) :
    S.filter (p ·) = S.filter (q ·) := by
  ext k
  simp only [Finset.mem_filter]
  exact ⟨fun hk => ⟨hk.1, (h k hk.1) ▸ hk.2⟩, fun hk => ⟨hk.1, (h k hk.1).symm ▸ hk.2⟩⟩

/-- …a filter that keeps nothing is empty… -/
theorem filter_eq_empty_on {S : Finset Name} {p : Name → Bool} (h : ∀ k ∈ S, p k = false) :
    S.filter (p ·) = ∅ := by
  ext k
  refine ⟨fun hk => ?_, fun hk => absurd hk (Finset.notMem_empty k)⟩
  obtain ⟨hs, hp⟩ := Finset.mem_filter.mp hk
  rw [h k hs] at hp
  exact Bool.noConfusion hp

/-- …and one that keeps everything is the set. -/
theorem filter_eq_self_on {S : Finset Name} {p : Name → Bool} (h : ∀ k ∈ S, p k = true) :
    S.filter (p ·) = S := by
  ext k
  simp only [Finset.mem_filter]
  exact ⟨fun hk => hk.1, fun hk => ⟨hk, h k hk⟩⟩

/-- `AdmA` at an object is its body's row. -/
theorem AdmA_object (b : Body) (a : Attr) : AdmA (.object b) a = AdmABody b a := rfl

/-- …and at a record, the row of every entry the map carries. -/
theorem AdmA_record (x : Term) (keys : Finset Name) (g : {k // k ∈ keys} → Attr) :
    AdmA (.record x) (.m keys g) = decide (∀ k : {k // k ∈ keys}, AdmA x (g k) = true) := rfl

/-- A literal table's lookup at a declared name. `MapOf.at_of_mem` says the same for an
    abstract table, and its `m.2 k` does not reduce when the table is written out, which is what
    the rows below need. -/
theorem MapOf.at_mk_pos {α : Type} {S : Finset Name} {f : {k // k ∈ S} → α} {k : Name}
    (h : k ∈ S) : MapOf.at ⟨S, f⟩ k = some (f ⟨k, h⟩) := dif_pos h

/-- …and at an undeclared name it answers nothing. -/
theorem MapOf.at_of_not_mem {α : Type} {m : MapOf α} {k : Name} (h : k ∉ m.1) :
    m.at k = none := dif_neg h

/-- An entry at a declared name goes through that name's field… -/
theorem entryCodec_mk_pos {S : Finset Name} {f : {k // k ∈ S} → FieldSem} {rc? : Option Codec}
    {k : Name} (h : k ∈ S) : entryCodec ⟨S, f⟩ rc? k = some (f ⟨k, h⟩).codec := by
  rw [entryCodec, MapOf.at_mk_pos h]

/-- …and at an undeclared one through the rest policy's. -/
theorem entryCodec_mk_neg {S : Finset Name} {f : {k // k ∈ S} → FieldSem} {rc? : Option Codec}
    {k : Name} (h : k ∉ S) : entryCodec ⟨S, f⟩ rc? k = rc? := by
  rw [entryCodec, MapOf.at_of_not_mem (m := ⟨S, f⟩) h]

/-- A body reads nothing that is not a map. -/
theorem AdmABody_of_not_m {c : Body} {a : Attr} (h : ∀ keys g, a ≠ .m keys g) :
    AdmABody c a = false := by
  cases c with
  | mk fields fld rest =>
    cases a with
    | m keys g => exact absurd rfl (h keys g)
    | _ => rfl

/-- The rows of a term list are as many as the terms. -/
theorem AdmAList_length (ts : List Term) : (AdmAList ts).length = ts.length := by
  induction ts with
  | nil => rfl
  | cons t ts ihx => simp only [AdmAList, List.length_cons, ihx]

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

/-- `opaque` reads an attribute exactly where its codec at that depth answers. -/
theorem AdmA_opaq_eq (a : Attr) :
    AdmA .opaq a = ((opaqCodec (Attr.depth a)).p a).isSome := rfl

/-- It reads every stored string, -/
theorem AdmA_opaq_str (s : String) : AdmA .opaq (.s s) = true := by
  rw [AdmA_opaq_eq, show Attr.depth (.s s) = 0 + 1 from rfl, opaqCodec_p_s]
  simp [stringCodec]

/-- …every stored boolean, -/
theorem AdmA_opaq_bool (b : Bool) : AdmA .opaq (.bool b) = true := by
  rw [AdmA_opaq_eq, show Attr.depth (.bool b) = 0 + 1 from rfl, opaqCodec_p_bool]
  simp [booleanCodec]

/-- …every stored byte string, -/
theorem AdmA_opaq_bin (b : Bytes) : AdmA .opaq (.b b) = true := by
  rw [AdmA_opaq_eq, show Attr.depth (.b b) = 0 + 1 from rfl, opaqCodec_p_b]
  simp [binaryCodec]

/-- …the stored null, -/
theorem AdmA_opaq_null : AdmA .opaq .null = true := by
  rw [AdmA_opaq_eq, show Attr.depth Attr.null = 0 + 1 from rfl, opaqCodec_p_null]
  simp [nullCodec]

-- the numeric read row, mirror of `Adm_opaq_num`
/-- …and every stored numeral, as `number` reads it. -/
theorem AdmA_opaq_num (x : WFNumeral) :
    AdmA .opaq (.n x) = (numberCodec.p (.n x)).isSome := by
  show ((opaqCodec (Attr.depth (.n x))).p (.n x)).isSome = _
  rw [show Attr.depth (.n x) = 0 + 1 from rfl, opaqCodec_p_n]

/-- A tuple with no tail pins the length of the wire list it reads. -/
theorem alignPA_none_length : ∀ {Ps : List AP} {as : List Attr},
    alignPA Ps none as = true → as.length = Ps.length := by
  intro Ps
  induction Ps with
  | nil => intro as h; cases as with
    | nil => rfl
    | cons _ _ => simp [alignPA] at h
  | cons p Ps' ihp =>
    intro as h
    cases as with
    | nil => simp [alignPA] at h
    | cons w as' =>
      simp only [alignPA, Bool.and_eq_true] at h
      simp [ihp h.2]

/-- Two tuples of one arity: the positions meet positionwise and the tails meet. -/
theorem alignPA_meet_zip :
    ∀ {Ps Qs Rs : List AP},
      List.Forall₂ (fun (pq : AP × AP) r => ∀ a, r a = (pq.1 a && pq.2 a)) (Ps.zip Qs) Rs →
      Ps.length = Qs.length →
    ∀ {pt qt rt : Option AP},
      ((pt = none ∧ qt = none ∧ rt = none) ∨
        ∃ p q r, pt = some p ∧ qt = some q ∧ rt = some r ∧ ∀ a, r a = (p a && q a)) →
    ∀ as, alignPA Rs rt as = (alignPA Ps pt as && alignPA Qs qt as) := by
  intro Ps Qs Rs hF hlen pt qt rt htl as
  induction as generalizing Ps Qs Rs with
  | nil =>
    cases Ps with
    | nil =>
      cases Qs with
      | nil =>
        cases hF
        rcases htl with ⟨rfl, rfl, rfl⟩ | ⟨p, q, r, rfl, rfl, rfl, _⟩ <;> simp [alignPA]
      | cons => simp only [List.length_nil, List.length_cons] at hlen; omega
    | cons p Ps' =>
      cases Qs with
      | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
      | cons q Qs' =>
        rw [List.zip_cons_cons] at hF
        cases hF with
        | cons _ _ => simp [alignPA]
  | cons a as ihw =>
    cases Ps with
    | nil =>
      cases Qs with
      | nil =>
        cases hF
        rcases htl with ⟨rfl, rfl, rfl⟩ | ⟨p, q, r, rfl, rfl, rfl, hr⟩
        · simp [alignPA]
        · simp only [alignPA, hr, ihw (Ps := []) (Qs := []) .nil rfl]
          simp [Bool.and_assoc, Bool.and_left_comm]
      | cons => simp only [List.length_nil, List.length_cons] at hlen; omega
    | cons p Ps' =>
      cases Qs with
      | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
      | cons q Qs' =>
        rw [List.zip_cons_cons] at hF
        cases hF with
        | cons hr hrest =>
          simp only [alignPA, hr, ihw hrest (by simpa using hlen)]
          simp [Bool.and_assoc, Bool.and_left_comm]

/-- `reqPresentT` in the form the object row uses: a declared name that must be read is
    present. -/
theorem reqPresentT_req (fields : Finset Name) (fld : {k // k ∈ fields} → ObjectSlot)
    (keys : Finset Name) :
    reqPresentT fields fld keys
      = decide (∀ k : {k // k ∈ fields}, ObjectSlot.isReq (fld k) = true → k.1 ∈ keys) := by
  unfold reqPresentT
  refine decide_eq_decide.mpr ⟨fun hh k hreq => ?_, fun hh k => ?_⟩
  · have hk := hh k
    cases hf : fld k with
    | req t => rw [hf] at hk; exact of_decide_eq_true hk
    | optional t => rw [hf] at hreq; exact absurd hreq (by simp [ObjectSlot.isReq])
  · cases hf : fld k with
    | req t => exact decide_eq_true (hh k (by rw [hf]; rfl))
    | optional t => rfl

/-- A declared name that must be read is a name the map carries. -/
theorem mem_keys_of_req {fields : Finset Name} {fld : {k // k ∈ fields} → ObjectSlot}
    {keys : Finset Name} (hv : reqPresentT fields fld keys = true) {k : {k // k ∈ fields}}
    (hf : ObjectSlot.isReq (fld k) = true) : k.1 ∈ keys := by
  have hh := of_decide_eq_true hv k
  cases hfd : fld k with
  | req t => rw [hfd] at hh; exact of_decide_eq_true hh
  | optional t => rw [hfd] at hf; exact absurd hf (by simp [ObjectSlot.isReq])

/-- A field at the bottom reads nothing either. -/
theorem AdmAField_of_isBottom {f : ObjectSlot} (h : ObjectSlot.isBottom f = true) (c : Attr) :
    AdmAField f c = false := by
  cases f with
  | req t => rw [show t = .never from eq_never_of_isNever h]; rfl
  | optional t => exact absurd h (by simp [ObjectSlot.isBottom])

/-- Where a literal reads, its base reads the same value: `literalCodec` is `baseCodec`
    restricted, and `Codec.restrict`'s `p` returns the base's own value where the guard passes. -/
theorem literal_p_base {k : GroundKind} {x : k.Carrier} {a : Attr} {v : Value}
    (h : (literalCodec k x).p a = some v) : (baseCodec k).p a = some v := by
  rw [literalCodec_p_restrict] at h
  simp only [Codec.restrict] at h
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
  simp only [Codec.restrict] at h
  cases hb : (baseCodec k).p a with
  | none => rw [hb] at h; simp at h
  | some w => rw [hb] at h; simp only [Option.bind] at h; split at h <;> simp_all


/-- **Two literals at one base and two values read nothing together.** Simp on `AdmALit` and
    `inL` does not reach the `number` row; exactness does. -/
theorem AdmALit_never_of_ne {k : GroundKind} {x y : k.Carrier} (hne : ¬ (x = y)) (a : Attr) :
    AdmA (.never : Term) a = (AdmA (Term.literal k x) a && AdmA (Term.literal k y) a) := by
  cases hx : AdmA (Term.literal k x) a with
  | false => simp [AdmA]
  | true =>
      cases hy : AdmA (Term.literal k y) a with
      | false => simp [AdmA]
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

/-- Every row that answers the bottom owes only its first half: the second is vacuous, because
    the first says no attribute is read by both factors. -/
theorem bottom_row {x y : Term}
    (h1 : ∀ a : Attr, AdmA (.never : Term) a = (AdmA x a && AdmA y a)) :
    (∀ a : Attr, AdmA (.never : Term) a = (AdmA x a && AdmA y a)) ∧
    (∀ a : Attr, AdmA x a = true → AdmA y a = true →
      (denote (.never : Term)).p a = (denote x).p a ∧
      (denote (.never : Term)).p a = (denote y).p a) :=
  ⟨h1, fun a ha hb => absurd (h1 a) (by rw [ha, hb]; simp [AdmA])⟩


/-- A traversal is a congruence in its element function, at the entries it visits. -/
theorem traverse_congr {α β : Type} {f g : α → Option β} :
    ∀ {xs : List α}, (∀ x ∈ xs, f x = g x) → traverse f xs = traverse g xs := by
  intro xs
  induction xs with
  | nil => intro _; rfl
  | cons x xs ihx =>
      intro hh
      rw [traverse_cons, traverse_cons, hh x (by simp),
        ihx (fun y hy => hh y (by simp [hy]))]

/-- **The `record` congruence.** The name set is the index, so the entry function is the only
    thing to compare. -/
theorem recordCodec_p_congr {c d : Codec} {keys : Finset Name} {g : {k // k ∈ keys} → Attr}
    (hh : ∀ k, c.p (g k) = d.p (g k)) :
    (recordCodec c).p (.m keys g) = (recordCodec d).p (.m keys g) := by
  show (funImage (fun k => c.p (g k))).map (Value.map keys)
      = (funImage (fun k => d.p (g k))).map (Value.map keys)
  rw [funext hh]


/-- `opaque` reads a self-identifying attribute exactly as the base for that attribute does. -/
theorem opaq_p_string (s : String) :
    (denote .opaq).p (.s s) = (denote (.string : Term)).p (.s s) := opaqCodec_p_s 0 s

/-- …a stored boolean as `boolean` does, -/
theorem opaq_p_boolean (b : Bool) :
    (denote .opaq).p (.bool b) = (denote (.boolean : Term)).p (.bool b) :=
  opaqCodec_p_bool 0 b

/-- …stored bytes as `binary` does, -/
theorem opaq_p_binary (b : Bytes) :
    (denote .opaq).p (.b b) = (denote (.binary : Term)).p (.b b) := opaqCodec_p_b 0 b

/-- …and the stored null as `null` does. -/
theorem opaq_p_null :
    (denote .opaq).p .null = (denote (.null : Term)).p .null := opaqCodec_p_null 0

/-- …and a stored numeral as `number` does. -/
theorem opaq_p_number (x : WFNumeral) :
    (denote .opaq).p (.n x) = (denote (.number : Term)).p (.n x) := by
  rw [show (denote .opaq).p (.n x) = (opaqCodec (0 + 1)).p (.n x) from rfl,
    opaqCodec_p_n]
  rfl

/-- `number`'s read row is its codec's domain, said as an equation so the `opaque` rows can
    conjoin the two. -/
theorem AdmA_number_eq (x : WFNumeral) :
    AdmA (.number : Term) (.n x) = (numberCodec.p (.n x)).isSome := rfl

/-- A declared position that holds nothing empties the tuple: every wire list the tuple
    reads fills each declared position. -/
theorem alignPA_never_false : ∀ {ts : List Term} {tail : Option Term} {ws : List Attr},
    ts.any Term.isNever = true → alignPA (AdmAList ts) (AdmAOptT tail) ws = false := by
  intro ts
  induction ts with
  | nil => intro _ _ h; simp at h
  | cons t ts' ih =>
    intro tail ws h
    cases ws with
    | nil => rfl
    | cons w ws' =>
      simp only [List.any_cons, Bool.or_eq_true] at h
      simp only [AdmAList, alignPA]
      rcases h with ht | hrest
      · rw [show t = Term.never from eq_never_of_isNever ht, show AdmA .never _ = false from rfl, Bool.false_and]
      · rw [ih (tail := tail) (ws := ws') hrest, Bool.and_false]


/-- A suffix holding the bottom reads nothing, on the read side. -/
theorem zipPA_never_false : ∀ {suf : List Term} {as : List Attr},
    suf.any Term.isNever = true → zipPA (AdmAList suf) as = false := by
  intro suf
  induction suf with
  | nil => intro _ h; simp at h
  | cons t ts' ih =>
    intro as h
    cases as with
    | nil => rfl
    | cons w as' =>
      simp only [List.any_cons, Bool.or_eq_true] at h
      simp only [AdmAList, zipPA]
      rcases h with ht | hrest
      · rw [show t = Term.never from eq_never_of_isNever ht,
          show AdmA .never w = false from rfl, Bool.false_and]
      · rw [ih (as := as') hrest, Bool.and_false]

/-- Normalising a list keeps what it reads. -/
theorem AdmA_listOf (pre : List Term) (sp : Option Term) (suf : List Term) (a : Attr) :
    AdmA (Term.listOf pre sp suf) a = AdmA (.list pre sp suf) a := by
  unfold Term.listOf
  split
  next hany =>
    cases a <;> simp only [AdmA] <;> try rfl
    refine Eq.symm ?_
    simp only [alignPAL]
    rcases Bool.or_eq_true .. |>.mp hany with hp | hs
    · rw [alignPA_never_false hp, Bool.false_and]
    · rw [zipPA_never_false hs, Bool.and_false]
  next => rfl

/-- Normalising a tuple keeps what it reads. -/
theorem AdmA_tupleOf (ts : List Term) (tail : Option Term) (v : Attr) :
    AdmA (Term.tupleOf ts tail) v = AdmA (.tuple ts tail) v :=
  AdmA_listOf ts tail [] v

/-- The read-side rows of a term list are that list mapped. -/
theorem AdmAList_eq_map (ts : List Term) : AdmAList ts = ts.map AdmA := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [AdmAList, List.map_cons, ih]

/-- …and the same for the spread. -/
theorem AdmAOptT_eq_map (sp : Option Term) : AdmAOptT sp = sp.map AdmA := by
  cases sp <;> rfl

/-- **The suffix row meets position by position**, on the read side. -/
theorem zipPA_meet {r₁ r₂ rz : List Term} (hlen : r₁.length = r₂.length)
    (hF : List.Forall₂ (fun (pq : Term × Term) w => ∀ b, AdmA w b = (AdmA pq.1 b && AdmA pq.2 b))
      (r₁.zip r₂) rz) :
    ∀ as, zipPA (AdmAList rz) as = (zipPA (AdmAList r₁) as && zipPA (AdmAList r₂) as) := by
  intro as
  induction as generalizing r₁ r₂ rz with
  | nil =>
      cases r₁ with
      | nil =>
          cases r₂ with
          | nil => cases hF; simp [zipPA, AdmAList]
          | cons => simp only [List.length_nil, List.length_cons] at hlen; omega
      | cons t r₁' =>
          cases r₂ with
          | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
          | cons u r₂' =>
              rw [List.zip_cons_cons] at hF
              cases hF with
              | cons _ _ => simp [zipPA, AdmAList]
  | cons b as ihb =>
      cases r₁ with
      | nil =>
          cases r₂ with
          | nil => cases hF; simp [zipPA, AdmAList]
          | cons => simp only [List.length_nil, List.length_cons] at hlen; omega
      | cons t r₁' =>
          cases r₂ with
          | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
          | cons u r₂' =>
              rw [List.zip_cons_cons] at hF
              cases hF with
              | cons hr hrest =>
                  simp only [AdmAList, zipPA, hr, ihb (by simpa using hlen) hrest]
                  simp [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]

/-- **The `list` meet's read-side admission obligation, read off the three rows.** The twin
    of `Adm_list_rows`. -/
theorem AdmA_list_rows {p₁ s₁ p₂ s₂ pz sz : List Term} {q₁ q₂ qz : Option Term}
    (hsome : ∀ n, (rowOfG pz qz sz n).isSome
      = ((rowOfG p₁ q₁ s₁ n).isSome && (rowOfG p₂ q₂ s₂ n).isSome))
    (hrel : ∀ n r₁ r₂ rz, rowOfG p₁ q₁ s₁ n = some r₁ → rowOfG p₂ q₂ s₂ n = some r₂ →
      rowOfG pz qz sz n = some rz →
      r₁.length = r₂.length ∧
        List.Forall₂ (fun (pq : Term × Term) w => ∀ b, AdmA w b = (AdmA pq.1 b && AdmA pq.2 b))
          (r₁.zip r₂) rz)
    (a : Attr) :
    AdmA (.list pz qz sz) a = (AdmA (.list p₁ q₁ s₁) a && AdmA (.list p₂ q₂ s₂) a) := by
  cases a with
  | l as =>
      have hb := hsome as.length
      simp only [AdmA, AdmAList_eq_map, AdmAOptT_eq_map, alignPAL_eq_rowOfG, rowOfG_map]
      cases h₁ : rowOfG p₁ q₁ s₁ as.length with
      | none =>
          rw [h₁] at hb
          simp only [Option.isSome_none, Bool.false_and] at hb
          cases hz : rowOfG pz qz sz as.length with
          | none => simp
          | some rz => rw [hz] at hb; simp at hb
      | some r₁ =>
          cases h₂ : rowOfG p₂ q₂ s₂ as.length with
          | none =>
              rw [h₁, h₂] at hb
              simp only [Option.isSome_some, Option.isSome_none, Bool.and_false] at hb
              cases hz : rowOfG pz qz sz as.length with
              | none => simp
              | some rz => rw [hz] at hb; simp at hb
          | some r₂ =>
              cases hz : rowOfG pz qz sz as.length with
              | none => rw [h₁, h₂, hz] at hb; simp at hb
              | some rz =>
                  obtain ⟨hlen, hF⟩ := hrel _ _ _ _ h₁ h₂ hz
                  simp only [Option.map_some]
                  simpa only [← AdmAList_eq_map] using zipPA_meet hlen hF as
  | _ => simp [AdmA]

/-- **`slots` is `rowOfG` with no suffix.** The codec-side row and the term-side row are one
    definition seen twice, which is what lets the reading agreement be stated over `rowOfG`
    like the admission. -/
theorem slots_eq_rowOfG : ∀ (cs : List Codec) (sp : Option Codec) (m : Nat),
    slots cs sp m = rowOfG cs sp [] m := by
  intro cs
  induction cs with
  | nil =>
      intro sp m
      cases sp with
      | none =>
          cases m with
          | zero =>
              rw [rowOfG_none_eq, if_pos (by simp only [List.length_nil]),
                List.append_nil]
              rfl
          | succ n =>
              rw [rowOfG_none_eq,
                if_neg (by simp only [List.length_nil, Nat.add_zero]; omega)]
              rfl
      | some c =>
          rw [slots_spread, rowOfG_some_eq,
            if_neg (by simp only [List.length_nil, Nat.add_zero]; omega)]
          simp only [List.length_nil, Nat.sub_zero, List.nil_append, List.append_nil]
  | cons c cs ih =>
      intro sp m
      cases m with
      | zero =>
          cases sp with
          | none =>
              rw [rowOfG_none_eq,
                if_neg (by simp only [List.length_cons, List.length_nil]; omega)]
              rfl
          | some d =>
              rw [rowOfG_some_eq,
                if_pos (by simp only [List.length_cons, List.length_nil]; omega)]
              rfl
      | succ n =>
          simp only [slots, ih]
          cases sp with
          | none =>
              simp only [rowOfG_none_eq, List.length_nil, Nat.add_zero, List.length_cons,
                List.append_nil]
              split
              · next he =>
                  rw [if_pos (by omega)]
                  simp only [Option.map_some, List.cons_append]
              · next he => rw [if_neg (by omega)]; rfl
          | some d =>
              simp only [rowOfG_some_eq, List.length_nil, Nat.add_zero, List.length_cons,
                List.append_nil]
              split
              · next he => rw [if_pos (by omega)]; rfl
              · next he =>
                  rw [if_neg (by omega),
                    show n + 1 - (cs.length + 1) = n - cs.length by omega]
                  simp only [Option.map_some, List.cons_append]

/-- …and `slotsL` is `rowOfG`. -/
theorem slotsL_eq_rowOfG (pre : List Codec) (sp : Option Codec) (suf : List Codec) (n : Nat) :
    slotsL pre sp suf n = rowOfG pre sp suf n := by
  unfold slotsL
  rw [slots_eq_rowOfG]
  cases sp with
  | none =>
      simp only [rowOfG_none_eq, List.length_nil, Nat.add_zero, List.append_nil]
      split
      · next hlt => rw [if_neg (by omega)]
      · next hge =>
          split
          · next he => rw [if_pos (by omega)]; simp
          · next he => rw [if_neg (by omega)]; simp
  | some c =>
      simp only [rowOfG_some_eq, List.length_nil, Nat.add_zero, List.append_nil]
      split
      · next hlt => rw [if_pos (by omega)]
      · next hge =>
          split
          · next hlt2 => rw [if_pos (by omega)]; simp
          · next hge2 =>
              rw [if_neg (by omega),
                show n - suf.length - pre.length = n - pre.length - suf.length by omega]
              simp

/-- Every position of an admitted row is admitted. -/
theorem zipPA_forall₂ : ∀ {r : List Term} {as : List Attr}, zipPA (AdmAList r) as = true →
    List.Forall₂ (fun t b => AdmA t b = true) r as := by
  intro r
  induction r with
  | nil =>
      intro as h
      cases as with
      | nil => exact .nil
      | cons => simp [zipPA, AdmAList] at h
  | cons t r' ih =>
      intro as h
      cases as with
      | nil => simp [zipPA, AdmAList] at h
      | cons b as' =>
          simp only [AdmAList, zipPA, Bool.and_eq_true] at h
          exact .cons h.1 (ih h.2)

/-- The spread a container denotes is the spread's own codec. -/
theorem denoteOpt_eq_map (sp : Option Term) : denoteOpt sp = sp.map denote := by
  cases sp <;> rfl

/-- **Two `list` shapes with no common length read nothing together.** -/
theorem AdmA_list_disjoint {p₁ s₁ p₂ s₂ : List Term} {q₁ q₂ : Option Term}
    (h : ∀ n, rowOfG p₁ q₁ s₁ n = none ∨ rowOfG p₂ q₂ s₂ n = none) (a : Attr) :
    (AdmA (.list p₁ q₁ s₁) a && AdmA (.list p₂ q₂ s₂) a) = false := by
  cases a with
  | l as =>
      simp only [AdmA, AdmAList_eq_map, AdmAOptT_eq_map, alignPAL_eq_rowOfG, rowOfG_map]
      rcases h as.length with hn | hn <;> simp [hn]
  | _ => simp [AdmA]


/-- A term that admits an attribute is not the bottom. -/
theorem not_isNever_of_admA {t : Term} {b : Attr} (hh : AdmA t b = true) : t.isNever = false := by
  cases t <;> first | rfl | exact absurd hh (by simp [AdmA])

/-! ### The count, on the read side

The mirror of §"The count, and what the meet does to it" above, one section at a time. -/

/-- A wire list a tuple aligns leaves no declared position at the bottom, so the normalised
    tuple is the tuple. -/
theorem alignPA_not_never : ∀ {vs : List Term} {tl : Option Term} {as : List Attr},
    alignPA (AdmAList vs) (AdmAOptT tl) as = true → vs.any Term.isNever = false := by
  intro vs
  induction vs with
  | nil => intro _ _ _; rfl
  | cons v vs' ihv =>
      intro tl as hh
      cases as with
      | nil => exact absurd hh (by simp [AdmAList, alignPA])
      | cons b as' =>
          simp only [AdmAList, alignPA, Bool.and_eq_true] at hh
          simp only [List.any_cons, Bool.or_eq_false_iff]
          exact ⟨not_isNever_of_admA hh.1, ihv hh.2⟩

/-- The aligned traversal, one declared position at a time. -/
theorem align_traverse_cons {c : Codec} {cs : List Codec} {tc : Option Codec} {b : Attr}
    {as : List Attr} :
    (align (c :: cs) tc (b :: as)).bind (traverse fun ca => ca.1.p ca.2)
      = (c.p b).bind fun y =>
          ((align cs tc as).bind (traverse fun ca => ca.1.p ca.2)).map (y :: ·) := by
  simp only [align]
  cases align cs tc as <;> simp [traverse_cons]

/-- …and one tail position at a time. -/
theorem align_traverse_tail_cons {c : Codec} {b : Attr} {as : List Attr} :
    (align [] (some c) (b :: as)).bind (traverse fun ca => ca.1.p ca.2)
      = (c.p b).bind fun y =>
          ((align [] (some c) as).bind (traverse fun ca => ca.1.p ca.2)).map (y :: ·) := by
  simp only [align]
  cases align ([] : List Codec) (some c) as <;> simp [traverse_cons]

/-- Normalising a refinement keeps what it reads. -/
theorem AdmA_refineOf (z : Term) (p : Pred) (a : Attr) :
    AdmA (Term.refineOf z p) a = AdmA (.refine z p) a := by
  cases z <;>
    first
      | rfl
      | (simp only [Term.refineOf]
         rename_i z' q
         split
         · rename_i r hr
           show (AdmA z' a && refineReads z' r.eval a)
               = ((AdmA z' a && refineReads z' q.eval a) && refineReads (.refine z' q) p.eval a)
           simp only [refineReads, denote_refine, Codec.restrict]
           cases hv : (denote z').p a with
           | none => simp
           | some v0 =>
               simp only [Option.bind_some]
               rw [meetM_eval hr v0]
               cases hq : q.eval v0 <;> simp [hq]
         · rename_i hr
           show false = ((AdmA z' a && refineReads z' q.eval a) && refineReads (.refine z' q) p.eval a)
           simp only [refineReads, denote_refine, Codec.restrict]
           cases hv : (denote z').p a with
           | none => simp
           | some v0 =>
               simp only [Option.bind_some]
               have he := meetM_empty hr v0
               cases hq : q.eval v0 <;> simp [hq] at he ⊢
               simp [he]
         · rfl)

/-- Normalising a refinement changes no reading at an attribute the inner term admits. -/
theorem refineOf_p {w : Term} {p : Pred} {a : Attr} (hw : AdmA w a = true) :
    (denote (Term.refineOf w p)).p a
      = ((denote w).p a).bind (fun v => if p.eval v then some v else none) := by
  cases w with
  | never => simp [AdmA] at hw
  | refine z' q =>
      obtain ⟨_, hq⟩ := Bool.and_eq_true_iff.mp
        (show (AdmA z' a && refineReads z' q.eval a) = true from hw)
      cases hv : (denote z').p a with
      | none => exact absurd ((refineReads_none hv).symm.trans hq) (by simp)
      | some v0 =>
        have hqv : q.eval v0 = true := (refineReads_some hv).symm.trans hq
        have hwv : (denote (.refine z' q)).p a = some v0 := by
          rw [denote_refine, Codec.restrict]
          show ((denote z').p a).bind (fun v => if q.eval v then some v else none) = some v0
          rw [hv]; simp [hqv]
        rw [hwv]
        simp only [Option.bind_some]
        simp only [Term.refineOf]
        split
        · rename_i r hr
          rw [denote_refine, Codec.restrict]
          show ((denote z').p a).bind (fun v => if r.eval v then some v else none) = _
          rw [hv]
          simp only [Option.bind_some]
          rw [meetM_eval hr v0, hqv, Bool.true_and]
        · rename_i hr
          have hp0 : p.eval v0 = false := by
            have he := meetM_empty hr v0
            rwa [hqv, Bool.true_and] at he
          rw [hp0]; rfl
        · rw [denote_refine, Codec.restrict]
          show (((denote z').p a).bind (fun v => if q.eval v then some v else none)).bind
              (fun v => if p.eval v then some v else none) = _
          rw [hv]; simp [hqv]
  | _ => rfl

/-- A refinement's gate reads the inner term, so terms that read alike gate alike. -/
theorem refineReads_congr {t u : Term} {q : Value → Bool} {a : Attr}
    (hh : (denote t).p a = (denote u).p a) : refineReads t q a = refineReads u q a := by
  simp only [refineReads, hh]

/-- **The refinement row, with the refinement on the left.** The predicate is data, so it rides
    on the meet of the inner terms; the reading agreement is what makes the gate agree. -/
theorem refine_row_l {x y w : Term} {p : Pred}
    (ih1 : ∀ b, AdmA w b = (AdmA x b && AdmA y b))
    (ih2 : ∀ b, AdmA x b = true → AdmA y b = true →
      (denote w).p b = (denote x).p b ∧ (denote w).p b = (denote y).p b) :
    (∀ a, AdmA (Term.refineOf w p) a = (AdmA (.refine x p) a && AdmA y a)) ∧
    (∀ a, AdmA (.refine x p) a = true → AdmA y a = true →
      (denote (Term.refineOf w p)).p a = (denote (.refine x p)).p a ∧
      (denote (Term.refineOf w p)).p a = (denote y).p a) := by
  constructor
  · intro a
    rw [AdmA_refineOf]
    show (AdmA w a && refineReads w p.eval a) = ((AdmA x a && refineReads x p.eval a) && AdmA y a)
    cases hw : AdmA w a with
    | false =>
        rw [ih1 a, Bool.and_eq_false_iff] at hw
        rcases hw with hx | hy
        · rw [hx]; simp
        · rw [hy]; simp
    | true =>
        have hxy := ih1 a
        rw [hw] at hxy
        have hx : AdmA x a = true := (Bool.and_eq_true .. ▸ hxy.symm : _).1
        have hy : AdmA y a = true := (Bool.and_eq_true .. ▸ hxy.symm : _).2
        rw [refineReads_congr (ih2 a hx hy).1, hx, hy]
        simp
  · intro a ha hb
    rw [show AdmA (.refine x p) a = (AdmA x a && refineReads x p.eval a) from rfl,
      Bool.and_eq_true] at ha
    obtain ⟨hx, hr⟩ := ha
    have hw : AdmA w a = true := by rw [ih1 a, hx, hb]; rfl
    obtain ⟨hd1, hd2⟩ := ih2 a hx hb
    cases hp : (denote x).p a with
    | none => rw [refineReads_none hp] at hr; exact absurd hr (by simp)
    | some v =>
        rw [refineReads_some hp] at hr
        have hwv : (denote w).p a = some v := hd1.trans hp
        have hyv : (denote y).p a = some v := hd2.symm.trans hwv
        refine ⟨?_, ?_⟩
        · rw [refineOf_p hw, hwv,
            show (denote (.refine x p)).p a
              = ((denote x).p a).bind (fun u => if p.eval u then some u else none) from rfl, hp]
        · simp [refineOf_p hw, hwv, hyv, hr]

/-- …and with the refinement on the right. -/
theorem refine_row_r {x y w : Term} {p : Pred}
    (ih1 : ∀ b, AdmA w b = (AdmA x b && AdmA y b))
    (ih2 : ∀ b, AdmA x b = true → AdmA y b = true →
      (denote w).p b = (denote x).p b ∧ (denote w).p b = (denote y).p b) :
    (∀ a, AdmA (Term.refineOf w p) a = (AdmA x a && AdmA (.refine y p) a)) ∧
    (∀ a, AdmA x a = true → AdmA (.refine y p) a = true →
      (denote (Term.refineOf w p)).p a = (denote x).p a ∧
      (denote (Term.refineOf w p)).p a = (denote (.refine y p)).p a) := by
  constructor
  · intro a
    rw [AdmA_refineOf]
    show (AdmA w a && refineReads w p.eval a) = (AdmA x a && (AdmA y a && refineReads y p.eval a))
    cases hw : AdmA w a with
    | false =>
        rw [ih1 a, Bool.and_eq_false_iff] at hw
        rcases hw with hx | hy
        · rw [hx]; simp
        · rw [hy]; simp
    | true =>
        have hxy := ih1 a
        rw [hw] at hxy
        have hx : AdmA x a = true := (Bool.and_eq_true .. ▸ hxy.symm : _).1
        have hy : AdmA y a = true := (Bool.and_eq_true .. ▸ hxy.symm : _).2
        rw [refineReads_congr (ih2 a hx hy).2, hx, hy]
        simp
  · intro a ha hb
    rw [show AdmA (.refine y p) a = (AdmA y a && refineReads y p.eval a) from rfl,
      Bool.and_eq_true] at hb
    obtain ⟨hy, hr⟩ := hb
    have hw : AdmA w a = true := by rw [ih1 a, ha, hy]; rfl
    obtain ⟨hd1, hd2⟩ := ih2 a ha hy
    cases hp : (denote y).p a with
    | none => rw [refineReads_none hp] at hr; exact absurd hr (by simp)
    | some v =>
        rw [refineReads_some hp] at hr
        have hwv : (denote w).p a = some v := hd2.trans hp
        have hxv : (denote x).p a = some v := hd1.symm.trans hwv
        refine ⟨?_, ?_⟩
        · simp [refineOf_p hw, hwv, hxv, hr]
        · rw [refineOf_p hw, hwv,
            show (denote (.refine y p)).p a
              = ((denote y).p a).bind (fun u => if p.eval u then some u else none) from rfl, hp]


/-- The options that survive are the ones that read; the bottoms read nothing. -/
theorem AdmAAny_filter_never : ∀ (ts : List Term) (v : Attr),
    AdmAAny (ts.filter (fun z => !z.isNever)) v = AdmAAny ts v
  | [], _ => rfl
  | t :: ts, v => by
      cases ht : t.isNever with
      | true =>
        have htn : t = Term.never := eq_never_of_isNever ht
        subst htn
        rw [List.filter_cons, if_neg (by simp [Term.isNever]), AdmAAny_cons,
          AdmAAny_filter_never ts v]
        rfl
      | false =>
        rw [List.filter_cons, if_pos (by simp [ht]), AdmAAny_cons, AdmAAny_cons,
          AdmAAny_filter_never ts v]


/-- The join over the met options is the join over the options, met with the partner. -/
theorem AdmAAny_meet {y : Term} (v : Attr) : ∀ {os zs : List Term},
    List.Forall₂ (fun t w => ∀ u, AdmA w u = (AdmA t u && AdmA y u)) os zs →
    AdmAAny zs v = (AdmAAny os v && AdmA y v) := by
  intro os zs h
  induction h with
  | nil => simp
  | cons hh _ ihx =>
    rw [AdmAAny_cons, AdmAAny_cons, hh v, ihx]
    cases AdmA _ v <;> cases AdmA y v <;> simp

/-- **`ofOptions` reads what its options read**, and no certificate is spent. -/
theorem AdmA_ofOptions (ts : List Term) (a : Attr) :
    AdmA (Term.ofOptions ts) a = AdmAAny ts a := by
  match ts with
  | [] => rfl
  | [t] => simp only [Term.ofOptions, AdmAAny_cons, AdmAAny_nil, Bool.or_false]
  | _ :: _ :: _ => exact selOptA_eq_AdmAAny _ a

/-- **The coproduct row of the meet needs no certificate, on the read side either.** -/
theorem union_meet_freeA {os zs : List Term} {y : Term} (a : Attr)
    (hR : List.Forall₂ (fun t w => ∀ b, AdmA w b = (AdmA t b && AdmA y b)) os zs) :
    AdmA (Term.ofOptions (zs.filter (fun z => !z.isNever))) a
      = (AdmA (.union os) a && AdmA y a) := by
  rw [AdmA_ofOptions, AdmAAny_filter_never, AdmAAny_meet a hR, AdmA_union, selOptA_eq_AdmAAny]


/-- A `Forall₂` relates every left element to some right one. -/
theorem forall₂_mem_left {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, List.Forall₂ R as bs → ∀ {x}, x ∈ as → ∃ y ∈ bs, R x y
  | _, _, .nil, _, hx => by simp at hx
  | _, _, .cons hr hrest, x, hx => by
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨_, List.mem_cons_self, hr⟩
      · obtain ⟨y, hy, hry⟩ := forall₂_mem_left hrest hx'
        exact ⟨y, List.mem_cons_of_mem _ hy, hry⟩

/-- **A union reads through its first reader.** -/
theorem union_p_find (ts : List Term) (a : Attr) :
    (denote (.union ts)).p a = (ts.find? (fun u => AdmA u a)).bind (fun t => (denote t).p a) := by
  rw [denote_union_sems]
  show select (optionSems ts) (·.admitA) (·.c.p) a = _
  unfold select
  rw [optionSems_eq, List.find?_map]
  have hq : ((fun o : OptionSem => o.admitA a) ∘ fun t => optionSemOf (denote t) (specOf t))
      = fun u => AdmA u a := by
    funext u
    show (optionSemOf (denote u) (specOf u)).admitA a = AdmA u a
    rw [admitOptA_eq (AdmA_exact u) a]; rfl
  rw [hq]
  cases ts.find? (fun u => AdmA u a) <;> simp [optionSemOf_c]

/-- …and so does a list of survivors, whatever its length. -/
theorem ofOptions_p_find (ts : List Term) (a : Attr) :
    (denote (Term.ofOptions ts)).p a
      = (ts.find? (fun u => AdmA u a)).bind (fun t => (denote t).p a) := by
  match ts with
  | [] => rfl
  | [s] =>
      show (denote s).p a = _
      cases h : AdmA s a with
      | true => simp [List.find?, h]
      | false =>
        have : (denote s).p a = none := by
          cases hp : (denote s).p a with
          | none => rfl
          | some _ => rw [(AdmA_exact s a).mpr (by rw [hp]; rfl)] at h; exact nomatch h
        simp [List.find?, h, this]
  | _ :: _ :: _ => exact union_p_find _ a

/-- **The first reader crosses a `Forall₂`** whose relation keeps the reading test. -/
theorem find?_forall₂ {α β : Type} {P : α → β → Prop} {p : α → Bool} {q : β → Bool}
    (hpq : ∀ t w, P t w → q w = p t) :
    ∀ {os : List α} {zs : List β}, List.Forall₂ P os zs →
      ∀ {t}, os.find? p = some t → ∃ w, zs.find? q = some w ∧ P t w
  | _, _, .nil, _, h => nomatch h
  | _, _, @List.Forall₂.cons _ _ _ t0 w0 _ _ hr hrest, t, h => by
      cases hp : p t0 with
      | true =>
        rw [List.find?_cons_of_pos hp] at h; cases h
        exact ⟨w0, List.find?_cons_of_pos (by rw [hpq _ _ hr, hp]), hr⟩
      | false =>
        rw [List.find?_cons_of_neg (by simp [hp])] at h
        obtain ⟨w, hw, hP⟩ := find?_forall₂ hpq hrest h
        exact ⟨w, by rw [List.find?_cons_of_neg (by simp [hpq _ _ hr, hp])]; exact hw, hP⟩

/-- Filtering out what cannot pass the test leaves the first passer. -/
theorem find?_filter_of {β : Type} {q keep : β → Bool} (h : ∀ w, q w = true → keep w = true) :
    ∀ zs : List β, (zs.filter keep).find? q = zs.find? q
  | [] => rfl
  | w :: zs => by
      cases hq : q w with
      | true => rw [List.filter_cons_of_pos (h w hq), List.find?_cons_of_pos hq,
          List.find?_cons_of_pos hq]
      | false =>
        rw [List.find?_cons_of_neg (by simp [hq])]
        cases hk : keep w with
        | true => rw [List.filter_cons_of_pos hk, List.find?_cons_of_neg (by simp [hq]),
            find?_filter_of h zs]
        | false => rw [List.filter_cons_of_neg (by simp [hk]), find?_filter_of h zs]

/-- A union that reads has a first reader. -/
theorem find?_of_AdmA_union {os : List Term} {a : Attr} (h : AdmA (.union os) a = true) :
    ∃ t, os.find? (fun u => AdmA u a) = some t := by
  rw [AdmA_union, selOptA_eq_AdmAAny] at h
  obtain ⟨t, ht, hta⟩ := AdmAAny_iff.mp h
  cases hf : os.find? (fun u => AdmA u a) with
  | some t' => exact ⟨t', rfl⟩
  | none => exact absurd hta (by simpa using List.find?_eq_none.mp hf t ht)

section StructuralAdmA
-- the object rows put the whole field table to `decide` under a binder
set_option maxHeartbeats 1000000

/-! ## The read side's homomorphism and its reading agreement, structurally

The same three layers the value side uses. The depth bounds are gone with the measure: the list
and tail lifts have measure-free twins here, and the object rows go through
`AdmA_object_of_slots`, which reads each body as its slot at every name. -/

/-- The conclusion of the read-side homomorphism, at one pair. -/
abbrev AdmAAt (x y z : Term) : Prop :=
  (∀ a : Attr, AdmA z a = (AdmA x a && AdmA y a)) ∧
  (∀ a : Attr, AdmA x a = true → AdmA y a = true →
    (denote z).p a = (denote x).p a ∧ (denote z).p a = (denote y).p a)

/-- `f` answers the read side with one term fixed on the left, at every right operand. -/
def AdmASound (x : Term) (f : Term → Option Term) : Prop :=
  ∀ y z, f y = some z → AdmAAt x y z

/-- …and over the operands the shared inner hands a family. -/
def AdmAFam (x : Term) (fam : Term → Option Term) : Prop :=
  ∀ y z, Delegated y → fam y = some z → AdmAAt x y z

/-- **Three rows that read every position alike read the whole list alike.** The answer's row
    and the two factors' rows agree at every position that both factors admit, so the three
    traversals agree. -/
theorem traverse_p_agree : ∀ {r₁ r₂ rz : List Term} {as : List Attr},
    List.Forall₂ (fun (pq : Term × Term) w => AdmAAt pq.1 pq.2 w) (r₁.zip r₂) rz →
    r₁.length = r₂.length →
    List.Forall₂ (fun t b => AdmA t b = true) r₁ as →
    List.Forall₂ (fun t b => AdmA t b = true) r₂ as →
    traverse (fun ca : Codec × Attr => ca.1.p ca.2) ((rz.map denote).zip as)
        = traverse (fun ca : Codec × Attr => ca.1.p ca.2) ((r₁.map denote).zip as) ∧
      traverse (fun ca : Codec × Attr => ca.1.p ca.2) ((rz.map denote).zip as)
        = traverse (fun ca : Codec × Attr => ca.1.p ca.2) ((r₂.map denote).zip as) := by
  intro r₁
  induction r₁ with
  | nil =>
      intro r₂ rz as hF hl ha hb
      cases r₂ with
      | nil => cases hF; cases ha; exact ⟨rfl, rfl⟩
      | cons => exact absurd hl (by simp only [List.length_nil, List.length_cons]; omega)
  | cons t r₁' ih =>
      intro r₂ rz as hF hl ha hb
      cases r₂ with
      | nil => exact absurd hl (by simp only [List.length_nil, List.length_cons]; omega)
      | cons u r₂' =>
          rw [List.zip_cons_cons] at hF
          cases hF with
          | cons hh ht =>
              cases ha with
              | cons hat hat' =>
                  cases hb with
                  | cons hbt hbt' =>
                      obtain ⟨hz1, hz2⟩ :=
                        ih ht (by simp only [List.length_cons] at hl; omega) hat' hbt'
                      obtain ⟨hp1, hp2⟩ := hh.2 _ hat hbt
                      refine ⟨?_, ?_⟩
                      · simp only [List.map_cons, List.zip_cons_cons, traverse_cons, hp1, hz1]
                      · simp only [List.map_cons, List.zip_cons_cons, traverse_cons, hp2, hz2]

/-- **The whole read-side obligation of the `list` meet, read off the three rows.** The
    admission half is `AdmA_list_rows`; the reading half is `traverse_p_agree` through
    `slotsL_eq_rowOfG`, which says the codec-side row and the term-side row are one row. -/
theorem AdmA_list_at {p₁ s₁ p₂ s₂ pz sz : List Term} {q₁ q₂ qz : Option Term}
    (hsome : ∀ n, (rowOfG pz qz sz n).isSome
      = ((rowOfG p₁ q₁ s₁ n).isSome && (rowOfG p₂ q₂ s₂ n).isSome))
    (hrel : ∀ n r₁ r₂ rz, rowOfG p₁ q₁ s₁ n = some r₁ → rowOfG p₂ q₂ s₂ n = some r₂ →
      rowOfG pz qz sz n = some rz →
      r₁.length = r₂.length ∧
        List.Forall₂ (fun (pq : Term × Term) w => AdmAAt pq.1 pq.2 w) (r₁.zip r₂) rz) :
    AdmAAt (.list p₁ q₁ s₁) (.list p₂ q₂ s₂) (.list pz qz sz) := by
  refine ⟨AdmA_list_rows hsome (fun n r₁ r₂ rz h1 h2 h3 => ?_), ?_⟩
  · obtain ⟨hlen, hF⟩ := hrel n r₁ r₂ rz h1 h2 h3
    exact ⟨hlen, hF.imp (fun _ _ h => h.1)⟩
  · intro a ha hb
    cases a with
    | l as =>
        simp only [AdmA, AdmAList_eq_map, AdmAOptT_eq_map, alignPAL_eq_rowOfG, rowOfG_map]
          at ha hb
        cases h₁ : rowOfG p₁ q₁ s₁ as.length with
        | none => rw [h₁] at ha; simp at ha
        | some r₁ =>
            cases h₂ : rowOfG p₂ q₂ s₂ as.length with
            | none => rw [h₂] at hb; simp at hb
            | some r₂ =>
                have hzs := hsome as.length
                rw [h₁, h₂] at hzs
                cases hz : rowOfG pz qz sz as.length with
                | none => rw [hz] at hzs; simp at hzs
                | some rz =>
                    obtain ⟨hlen, hF⟩ := hrel _ _ _ _ h₁ h₂ hz
                    rw [h₁] at ha
                    rw [h₂] at hb
                    simp only [Option.map_some, ← AdmAList_eq_map] at ha hb
                    obtain ⟨hq1, hq2⟩ :=
                      traverse_p_agree hF hlen (zipPA_forall₂ ha) (zipPA_forall₂ hb)
                    simp only [denote_list, listCodec, alignL, denoteList_eq, denoteOpt_eq_map,
                      slotsL_eq_rowOfG, rowOfG_map, h₁, h₂, hz, Option.map_some,
                      Option.bind_some]
                    exact ⟨congrArg (Option.map Value.arr) hq1,
                      congrArg (Option.map Value.arr) hq2⟩
    | _ => simp [AdmA] at ha


mutual
/-- Every row that reads the right operand alone reads what the family reads. -/
theorem admA_meetSRight {x : Term} {fam : Term → Option Term} (hf : AdmAFam x fam) :
    ∀ y z, meetSRight fam y = some z → AdmAAt x y z
  | .never, _, h => by
      simp only [meetSRight, Option.some.injEq] at h; subst h
      exact ⟨fun a => by simp [AdmA], fun a _ hb => absurd hb (by simp [AdmA])⟩
  | .held _ _ _ _, _, h => by simp [meetSRight] at h
  | .lazy t, _, h => by
      rw [meetSRight] at h
      obtain ⟨ih1, ih2⟩ := admA_meetSRight hf t _ h
      exact ⟨fun a => by simpa [AdmA] using ih1 a,
        fun a ha hb => ih2 a ha (by simpa [AdmA] using hb)⟩
  | .refine y p, _, h => by
      simp only [meetSRight] at h
      split at h
      · obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨ih1, ih2⟩ := admA_meetSRight hf y w hw
        exact refine_row_r ih1 ih2
      · exact absurd h (by simp)
  | .union os, _, h => by
      obtain ⟨zs, hF, rfl⟩ := meetSRight_union h
      have hB := admA_meetSRightL hf os zs hF
      refine ⟨fun a => ?_, fun a ha hb => ?_⟩
      · rw [Bool.and_comm]
        exact union_meet_freeA a (List.Forall₂.imp (fun _ _ hh => hh.1) hB)
      · obtain ⟨t, hft⟩ := find?_of_AdmA_union hb
        have hta : AdmA t a = true := List.find?_some (p := fun u => AdmA u a) hft
        obtain ⟨w, hfw, hwA, hwP⟩ :=
          find?_forall₂ (q := fun u => AdmA u a) (fun _ _ hh => by rw [hh.1 a, ha, Bool.and_true])
            hB hft
        rw [ofOptions_p_find, find?_filter_of (fun w hw => by rw [not_isNever_of_admA hw]; rfl),
          hfw, union_p_find, hft]
        exact ⟨(hwP a hta ha).2, (hwP a hta ha).1⟩
  | .string, _, h => hf .string _ trivial h
  | .number, _, h => hf .number _ trivial h
  | .boolean, _, h => hf .boolean _ trivial h
  | .binary, _, h => hf .binary _ trivial h
  | .null, _, h => hf .null _ trivial h
  | .literal k lv, _, h => hf (.literal k lv) _ trivial h
  | .set b, _, h => hf (.set b) _ trivial h
  | .opaq, _, h => hf .opaq _ trivial h
  | .list p q s, _, h => hf (.list p q s) _ trivial h
  | .object b, _, h => hf (.object b) _ trivial h
termination_by structural y => y

/-- The union row's options, lifted pointwise. -/
theorem admA_meetSRightL {x : Term} {fam : Term → Option Term} (hf : AdmAFam x fam) :
    ∀ os zs, List.Forall₂ (fun t w => meetSRight fam t = some w) os zs →
      List.Forall₂ (fun t w =>
        (∀ b, AdmA w b = (AdmA t b && AdmA x b)) ∧
        (∀ b, AdmA t b = true → AdmA x b = true →
          (denote w).p b = (denote t).p b ∧ (denote w).p b = (denote x).p b)) os zs
  | [], _, h => by cases h; exact .nil
  | t :: ts, _, h => by
      cases h with
      | cons hh ht =>
          obtain ⟨h1, h2⟩ := admA_meetSRight hf t _ hh
          exact .cons ⟨fun b => by rw [h1 b, Bool.and_comm],
            fun b hbt hbx => ⟨(h2 b hbx hbt).2, (h2 b hbx hbt).1⟩⟩ (admA_meetSRightL hf ts _ ht)
termination_by structural os => os
end

/-- The catch-all of every family: two constructors in different attribute slots read nothing
    together, so the pair is the bottom. -/
local macro "admA_never" fam:ident : tactic => `(tactic|
  (simp only [$fam:ident, Option.some.injEq] at *
   subst_vars
   refine bottom_row (fun a => ?_)
   first
     | (refine Eq.trans ?g1 (AdmA_and_false ?g2 a).symm
        case g2 =>
          first
            | rfl
            | (cases ‹GroundKind› <;> rfl)
            | (cases ‹SetBase› <;> rfl)
            | (cases ‹GroundKind› <;> cases ‹SetBase› <;> rfl)
        case g1 => rfl)
     | (cases a <;> simp [AdmA, inD])))

/-- The base row: the same constructor on both sides is reflexive on both halves. -/
theorem admA_same (x : Term) : AdmAAt x x x :=
  ⟨fun a => (Bool.and_self _).symm, fun a _ _ => ⟨rfl, rfl⟩⟩

/-- `string` reads `S`, and what it meets reads the same attribute. -/
theorem admA_famString : AdmAFam Term.string famString := by
  intro y z hd h
  cases y <;> first | exact hd.elim | skip
  case string => simp only [famString, Option.some.injEq] at h; subst h; exact admA_same _
  case literal k lv =>
      cases k <;> simp only [famString, Option.some.injEq, reduceCtorEq] at h <;>
        (try subst h) <;>
        first
          | (refine ⟨fun a => ?_, fun a ha hb => ⟨literal_denote_agree hb, rfl⟩⟩
             cases hx : AdmA (Term.literal _ _) a with
             | false => simp
             | true => rw [AdmA_base_of_literal rfl hx]; simp)
          | (refine bottom_row (fun a => ?_)
             cases a <;> simp_all [AdmA, AdmALit, inL, inD, literalCodec,
               Codec.restrict, baseCodec])
  case opaq =>
      simp only [famString, Option.some.injEq] at h; subst h
      refine ⟨fun a => ?_, fun a ha hb => ?_⟩
      · cases a <;>
          (try simp only [AdmA_opaq_str, AdmA_opaq_bool, AdmA_opaq_bin, AdmA_opaq_null]) <;>
          simp [AdmA]
      · cases a <;> refine ⟨?_, ?_⟩ <;>
          simp_all [AdmA, opaq_p_string, opaq_p_boolean, opaq_p_binary, opaq_p_null]
  all_goals admA_never famString

/-- `boolean` reads `BOOL`, and what it meets reads the same attribute. -/
theorem admA_famBoolean : AdmAFam Term.boolean famBoolean := by
  intro y z hd h
  cases y <;> first | exact hd.elim | skip
  case boolean => simp only [famBoolean, Option.some.injEq] at h; subst h; exact admA_same _
  case literal k lv =>
      simp only [famBoolean] at h
      split at h
      next hk =>
        subst hk
        simp only [Option.some.injEq] at h; subst h
        refine ⟨fun a => ?_, fun a ha hb => ⟨literal_denote_agree hb, rfl⟩⟩
        cases hx : AdmA (Term.literal _ _) a with
        | false => simp
        | true => rw [AdmA_base_of_literal rfl hx]; simp
      next hk =>
        simp only [Option.some.injEq] at h; subst h
        refine bottom_row (fun a => ?_)
        cases k <;> cases a <;> simp_all [AdmA, AdmALit, inL, inD, literalCodec,
          Codec.restrict, baseCodec]
  case opaq =>
      simp only [famBoolean, Option.some.injEq] at h; subst h
      refine ⟨fun a => ?_, fun a ha hb => ?_⟩
      · cases a <;>
          (try simp only [AdmA_opaq_str, AdmA_opaq_bool, AdmA_opaq_bin, AdmA_opaq_null]) <;>
          simp [AdmA]
      · cases a <;> refine ⟨?_, ?_⟩ <;>
          simp_all [AdmA, opaq_p_string, opaq_p_boolean, opaq_p_binary, opaq_p_null]
  all_goals admA_never famBoolean

/-- `binary` reads `B`, and what it meets reads the same attribute. -/
theorem admA_famBinary : AdmAFam Term.binary famBinary := by
  intro y z hd h
  cases y <;> first | exact hd.elim | skip
  case binary => simp only [famBinary, Option.some.injEq] at h; subst h; exact admA_same _
  case literal k lv =>
      simp only [famBinary] at h
      split at h
      next hk =>
        subst hk
        simp only [Option.some.injEq] at h; subst h
        refine ⟨fun a => ?_, fun a ha hb => ⟨literal_denote_agree hb, rfl⟩⟩
        cases hx : AdmA (Term.literal _ _) a with
        | false => simp
        | true => rw [AdmA_base_of_literal rfl hx]; simp
      next hk =>
        simp only [Option.some.injEq] at h; subst h
        refine bottom_row (fun a => ?_)
        cases k <;> cases a <;> simp_all [AdmA, AdmALit, inL, inD, literalCodec,
          Codec.restrict, baseCodec]
  case opaq =>
      simp only [famBinary, Option.some.injEq] at h; subst h
      refine ⟨fun a => ?_, fun a ha hb => ?_⟩
      · cases a <;>
          (try simp only [AdmA_opaq_str, AdmA_opaq_bool, AdmA_opaq_bin, AdmA_opaq_null]) <;>
          simp [AdmA]
      · cases a <;> refine ⟨?_, ?_⟩ <;>
          simp_all [AdmA, opaq_p_string, opaq_p_boolean, opaq_p_binary, opaq_p_null]
  all_goals admA_never famBinary

/-- `null` reads `NULL`, and what it meets reads the same attribute. -/
theorem admA_famNull : AdmAFam Term.null famNull := by
  intro y z hd h
  cases y <;> first | exact hd.elim | skip
  case null => simp only [famNull, Option.some.injEq] at h; subst h; exact admA_same _
  case literal k lv =>
      simp only [famNull] at h
      split at h
      next hk =>
        subst hk
        simp only [Option.some.injEq] at h; subst h
        refine ⟨fun a => ?_, fun a ha hb => ⟨literal_denote_agree hb, rfl⟩⟩
        cases hx : AdmA (Term.literal _ _) a with
        | false => simp
        | true => rw [AdmA_base_of_literal rfl hx]; simp
      next hk =>
        simp only [Option.some.injEq] at h; subst h
        refine bottom_row (fun a => ?_)
        cases k <;> cases a <;> simp_all [AdmA, AdmALit, inL, inD, literalCodec,
          Codec.restrict, baseCodec]
  case opaq =>
      simp only [famNull, Option.some.injEq] at h; subst h
      refine ⟨fun a => ?_, fun a ha hb => ?_⟩
      · cases a <;>
          (try simp only [AdmA_opaq_str, AdmA_opaq_bool, AdmA_opaq_bin, AdmA_opaq_null]) <;>
          simp [AdmA]
      · cases a <;> refine ⟨?_, ?_⟩ <;>
          simp_all [AdmA, opaq_p_string, opaq_p_boolean, opaq_p_binary, opaq_p_null]
  all_goals admA_never famNull

/-- `number` reads a stored numeral. -/
theorem admA_famNumber : AdmAFam Term.number famNumber := by
  intro y z hd h
  cases y <;> first | exact hd.elim | skip
  case number => simp only [famNumber, Option.some.injEq] at h; subst h; exact admA_same _
  case literal k lv =>
      cases k <;> simp only [famNumber, Option.some.injEq, reduceCtorEq] at h <;>
        (try subst h) <;>
        first
          | (refine ⟨fun a => ?_, fun a ha hb => ⟨literal_denote_agree hb, rfl⟩⟩
             cases hx : AdmA (Term.literal _ _) a with
             | false => simp
             | true => rw [AdmA_base_of_literal rfl hx]; simp)
          | (refine bottom_row (fun a => ?_)
             cases a <;> simp_all [AdmA, AdmALit, inL, inD, literalCodec,
               Codec.restrict, baseCodec])
  case opaq =>
      simp only [famNumber, Option.some.injEq] at h; subst h
      refine ⟨fun a => ?_, fun a ha hb => ?_⟩
      · cases a <;>
          (try simp only [AdmA_opaq_num, AdmA_number_eq, Bool.and_self]) <;>
          simp [AdmA]
      · cases a <;> refine ⟨?_, ?_⟩ <;> simp_all [AdmA, opaq_p_number]
  all_goals admA_never famNumber

/-- A literal reads its own value and nothing else, and its base reads it too. -/
theorem admA_famLit (k : GroundKind) (lv : k.Carrier) :
    AdmAFam (.literal k lv) (famLit k lv) := by
  intro y z hd h
  cases y <;> first | exact hd.elim | skip
  case literal k' lv' =>
      simp only [famLit] at h
      cases k <;> cases k' <;> simp only [Term.meetLit, reduceCtorEq] at h <;>
        (try split at h) <;>
        (try (simp only [Option.some.injEq] at h
              subst h
              subst_vars
              first
                | exact admA_same _
                | (refine bottom_row (fun a => ?_)
                   first
                     | exact AdmALit_never_of_ne (by assumption) a
                     | exact Eq.trans rfl (AdmA_and_false (by first | rfl | decide) a).symm)))
  case string | number | boolean | binary | null =>
      cases k <;>
        simp only [famLit, reduceCtorEq, reduceIte, Option.some.injEq] at h <;>
        (try subst h) <;>
        first
          | (refine ⟨fun a => ?_, fun a ha hb => ⟨rfl, literal_denote_agree ha⟩⟩
             cases hx : AdmA (Term.literal _ _) a with
             | false => simp
             | true => rw [AdmA_base_of_literal rfl hx]; simp)
          | (refine bottom_row (fun a => ?_)
             exact Eq.trans rfl (AdmA_and_false (by first | rfl | decide) a).symm)
  case opaq => simp [famLit] at h
  all_goals admA_never famLit

/-- Two set bases read together where they are equal. -/
theorem admA_famSet (b : SetBase) : AdmAFam (.set b) (famSet b) := by
  intro y z hd h
  cases y <;> first | exact hd.elim | skip
  case set b' =>
      cases b <;> cases b' <;>
        simp only [famSet, reduceCtorEq, reduceIte, Option.some.injEq] at h <;>
        (try subst h) <;>
        first
          | exact admA_same _
          | (refine bottom_row (fun a => ?_)
             cases a <;> simp_all [AdmA, AdmASet])
  case opaq => simp [famSet] at h
  all_goals admA_never famSet

/-- `opaque` reads each self-identifying base, and meets another `opaque` as itself. -/
theorem admA_famOpaq : AdmAFam .opaq (famOpaq) := by
  intro y z hd h
  cases y <;> first | exact hd.elim | skip
  case string | boolean | binary | null =>
      simp only [famOpaq, Option.some.injEq] at h; subst h
      refine ⟨fun a => ?_, fun a ha hb => ?_⟩
      · cases a <;>
          (try simp only [AdmA_opaq_str, AdmA_opaq_bool, AdmA_opaq_bin, AdmA_opaq_null]) <;>
          simp [AdmA]
      · cases a <;> refine ⟨?_, ?_⟩ <;>
          simp_all [AdmA, opaq_p_string, opaq_p_boolean, opaq_p_binary, opaq_p_null]
  case number =>
      simp only [famOpaq, Option.some.injEq] at h; subst h
      refine ⟨fun a => ?_, fun a ha hb => ?_⟩
      · cases a <;>
          (try simp only [AdmA_opaq_num, AdmA_number_eq, Bool.and_self]) <;>
          simp [AdmA]
      · cases a <;> refine ⟨?_, ?_⟩ <;> simp_all [AdmA, opaq_p_number]
  case opaq =>
      simp only [famOpaq, Option.some.injEq] at h; subst h
      exact admA_same _
  all_goals simp [famOpaq] at h


/-! ### The container families. The lifts are measure-free. -/

/-- Both halves at one element, from the soundness of the call the family carries. -/
theorem admA_split {e : Term} {f : Term → Option Term} (hf : AdmASound e f)
    {t v : Term} (hv : f t = some v) (b : Attr) (hb : AdmA v b = true) :
    AdmA e b = true ∧ AdmA t b = true ∧
      (denote v).p b = (denote e).p b ∧ (denote v).p b = (denote t).p b := by
  obtain ⟨h1, h2⟩ := hf t v hv
  rw [h1 b, Bool.and_eq_true] at hb
  exact ⟨hb.1, hb.2, h2 b hb.1 hb.2⟩

/-! ### The tuple lifts, zipped and measure-free. -/

/-- Two tuples' positions, zipped and lifted pointwise. -/
theorem admAList_zip_lift :
    ∀ {ts us : List Term} {fs : List (Term → Option Term)} {vs : List Term},
      List.Forall₂ AdmASound ts fs →
      List.Forall₂ (fun (p : (Term → Option Term) × Term) v => p.1 p.2 = some v) (fs.zip us) vs →
      List.Forall₂ (fun (pq : AP × AP) r => ∀ w, r w = (pq.1 w && pq.2 w))
        ((AdmAList ts).zip (AdmAList us)) (AdmAList vs) := by
  intro ts
  induction ts with
  | nil => intro us fs vs hfs hF; cases hfs; rw [List.zip_nil_left] at hF; cases hF; exact .nil
  | cons t ts' ihx =>
      intro us fs vs hfs hF
      cases hfs with
      | cons hf hfs' =>
          cases us with
          | nil => rw [List.zip_nil_right] at hF; cases hF; exact .nil
          | cons u us' =>
              cases hF with
              | cons hh ht => exact .cons (fun w => (hf u _ hh).1 w) (ihx hfs' ht)

/-- **Normalisation keeps the read-side obligation.** Where a declared position is the bottom
    the answer admits no attribute, so the reading half is vacuous and the bottom stands. -/
theorem AdmAAt_listOf {x y : Term} {pre suf : List Term} {sp : Option Term}
    (h : AdmAAt x y (.list pre sp suf)) : AdmAAt x y (Term.listOf pre sp suf) := by
  rcases listOf_cases pre sp suf with hc | hc
  · rw [hc]
    refine bottom_row (fun a => ?_)
    rw [← h.1 a, ← AdmA_listOf, hc]
  · rw [hc]; exact h

/-- Two rows of terms, the left as partially applied meets, met position by position on the
    read side. The term-level twin of `admAList_zip_lift`. -/
theorem zipF_lift_termsA :
    ∀ {ts us : List Term} {fs : List (Term → Option Term)} {vs : List Term},
      List.Forall₂ AdmASound ts fs →
      List.Forall₂ (fun (p : (Term → Option Term) × Term) v => p.1 p.2 = some v) (fs.zip us) vs →
      List.Forall₂ (fun (pq : Term × Term) w => AdmAAt pq.1 pq.2 w) (ts.zip us) vs := by
  intro ts
  induction ts with
  | nil => intro us fs vs hfs hv; cases hfs; cases hv; exact .nil
  | cons t ts ihs =>
      intro us fs vs hfs hv
      cases hfs with
      | cons hsound hfs' =>
          cases us with
          | nil => cases hv; exact .nil
          | cons u us =>
              cases hv with
              | cons hh ht => exact .cons (hsound u _ hh) (ihs hfs' ht)

/-- **The one positional container's family, on the read side.** The same three branches the
    value side takes, with `AdmA_list_at` in place of `Adm_list_rows`. -/
theorem admA_famList {pre suf : List Term} {sp : Option Term}
    {fpre fsuf : List (Term → Option Term)} {fsp : Option (Term → Option Term)}
    (hp : List.Forall₂ AdmASound pre fpre)
    (hs : (sp = none ∧ fsp = none) ∨ ∃ t f, sp = some t ∧ fsp = some f ∧ AdmASound t f)
    (hf : List.Forall₂ AdmASound suf fsuf) :
    AdmAFam (.list pre sp suf) (famList fpre fsp fsuf) := by
  have hlp := hp.length_eq
  have hlf := hf.length_eq
  intro y z hd h
  cases y <;> first | exact hd.elim | skip
  case list pre₂ sp₂ suf₂ =>
      simp only [famList] at h
      rcases hs with ⟨rfl, rfl⟩ | ⟨t, f, rfl, rfl, hsound⟩
      · simp only [listMeetRow] at h
        rw [show rowOfG fpre none fsuf (fpre.length + fsuf.length) = some (fpre ++ fsuf) from
          by rw [rowOfG_none_eq, if_pos rfl]] at h
        have hlen0 : fpre.length + fsuf.length = pre.length + suf.length := by omega
        rw [hlen0] at h
        cases hR : rowOfG pre₂ sp₂ suf₂ (pre.length + suf.length) with
        | none =>
            rw [hR] at h
            simp only [Option.some.injEq] at h
            subst h
            have hdis : ∀ n, rowOfG pre none suf n = none ∨ rowOfG pre₂ sp₂ suf₂ n = none := by
              intro n
              cases hd2 : decide (n = pre.length + suf.length) with
              | true => simp only [decide_eq_true_eq] at hd2; subst hd2; exact Or.inr hR
              | false =>
                  simp only [decide_eq_false_iff_not] at hd2
                  exact Or.inl (by rw [rowOfG_none_eq, if_neg hd2])
            exact bottom_row (fun a => (AdmA_list_disjoint hdis a).symm)
        | some us =>
            rw [hR] at h
            obtain ⟨row, hrow, rfl⟩ := Option.map_eq_some_iff.mp h
            have hus : us.length = pre.length + suf.length := rowOfG_length hR
            have hFz : List.Forall₂
                (fun (p : (Term → Option Term) × Term) w => p.1 p.2 = some w)
                ((fpre ++ fsuf).zip us) row :=
              allSome_map_forall₂ _ (by rw [← zipF_eq]; exact hrow)
            have hrowlen : row.length = pre.length + suf.length := by
              have hz := hFz.length_eq
              simp only [List.length_zip, List.length_append, hus] at hz
              omega
            have hrel₀ := zipF_lift_termsA (forall₂_append hp hf) hFz
            refine AdmAAt_listOf ?_
            refine AdmA_list_at (p₁ := pre) (q₁ := none) (s₁ := suf) ?_ ?_
            · intro n
              simp only [rowOfG_none_eq, List.length_nil, Nat.add_zero, hrowlen]
              cases hd2 : decide (n = pre.length + suf.length) with
              | true =>
                  simp only [decide_eq_true_eq] at hd2
                  subst hd2
                  rw [if_pos rfl, if_pos rfl, hR]
                  simp
              | false =>
                  simp only [decide_eq_false_iff_not] at hd2
                  rw [if_neg hd2, if_neg hd2]
                  simp
            · intro n r₁ r₂ rz h1 h2 h3
              rw [rowOfG_none_eq] at h1 h3
              simp only [List.length_nil, Nat.add_zero, hrowlen] at h3
              split at h1
              · next he =>
                  simp only [Option.some.injEq] at h1
                  subst h1
                  subst he
                  rw [if_pos rfl] at h3
                  simp only [Option.some.injEq] at h3
                  subst h3
                  rw [hR] at h2
                  simp only [Option.some.injEq] at h2
                  subst h2
                  exact ⟨by simp only [List.length_append]; omega, by simpa using hrel₀⟩
              · exact absurd h1 (by simp)
      · cases sp₂ with
        | none =>
            simp only [listMeetRow] at h
            rw [show rowOfG pre₂ none suf₂ (pre₂.length + suf₂.length)
                = some (pre₂ ++ suf₂) from by rw [rowOfG_none_eq, if_pos rfl]] at h
            cases hL : rowOfG fpre (some f) fsuf (pre₂.length + suf₂.length) with
            | none =>
                rw [hL] at h
                simp only [Option.some.injEq] at h
                subst h
                have hshort : pre₂.length + suf₂.length < fpre.length + fsuf.length := by
                  rw [rowOfG_some_eq] at hL
                  split at hL
                  · omega
                  · exact absurd hL (by simp)
                have hdis : ∀ n,
                    rowOfG pre (some t) suf n = none ∨ rowOfG pre₂ none suf₂ n = none := by
                  intro n
                  cases hd2 : decide (n = pre₂.length + suf₂.length) with
                  | true =>
                      simp only [decide_eq_true_eq] at hd2
                      subst hd2
                      exact Or.inl (by rw [rowOfG_some_eq, if_pos (by omega)])
                  | false =>
                      simp only [decide_eq_false_iff_not] at hd2
                      exact Or.inr (by rw [rowOfG_none_eq, if_neg hd2])
                exact bottom_row (fun a => (AdmA_list_disjoint hdis a).symm)
            | some fs =>
                rw [hL] at h
                obtain ⟨row, hrow, rfl⟩ := Option.map_eq_some_iff.mp h
                obtain ⟨ts, hts, htsF⟩ :=
                  rowOfG_forall₂_left hp (Or.inr ⟨t, f, rfl, rfl, hsound⟩) hf hL
                have hmin : pre.length + suf.length ≤ pre₂.length + suf₂.length := by
                  rw [rowOfG_some_eq] at hL
                  split at hL
                  · exact absurd hL (by simp)
                  · omega
                have hfs : fs.length = pre₂.length + suf₂.length := rowOfG_length hL
                have hFz : List.Forall₂
                    (fun (p : (Term → Option Term) × Term) w => p.1 p.2 = some w)
                    (fs.zip (pre₂ ++ suf₂)) row :=
                  allSome_map_forall₂ _ (by rw [← zipF_eq]; exact hrow)
                have hrowlen : row.length = pre₂.length + suf₂.length := by
                  have hz := hFz.length_eq
                  simp only [List.length_zip, List.length_append, hfs] at hz
                  omega
                have hrel₀ := zipF_lift_termsA htsF hFz
                refine AdmAAt_listOf ?_
                refine AdmA_list_at (p₁ := pre) (q₁ := some t) (s₁ := suf) ?_ ?_
                · intro n
                  simp only [rowOfG_none_eq, rowOfG_some_eq, List.length_nil, Nat.add_zero,
                    hrowlen]
                  cases hd2 : decide (n = pre₂.length + suf₂.length) with
                  | true =>
                      simp only [decide_eq_true_eq] at hd2
                      subst hd2
                      rw [if_pos rfl, if_neg (by omega), if_pos rfl]
                      simp
                  | false =>
                      simp only [decide_eq_false_iff_not] at hd2
                      rw [if_neg hd2, if_neg hd2]
                      simp
                · intro n r₁ r₂ rz h1 h2 h3
                  rw [rowOfG_none_eq] at h2 h3
                  simp only [List.length_nil, Nat.add_zero, hrowlen] at h3
                  split at h2
                  · next he =>
                      simp only [Option.some.injEq] at h2
                      subst h2
                      subst he
                      rw [if_pos rfl] at h3
                      simp only [Option.some.injEq] at h3
                      subst h3
                      rw [hts] at h1
                      simp only [Option.some.injEq] at h1
                      subst h1
                      refine ⟨?_, by simpa using hrel₀⟩
                      have hl := rowOfG_length hts
                      simp only [List.length_append]
                      omega
                  · exact absurd h2 (by simp)
        | some c =>
            simp only [listMeetRow] at h
            split at h
            · next hdom =>
                obtain ⟨fs, hfs⟩ :=
                  rowOfG_total (pre := fpre) (suf := fsuf) (c := f)
                    (n := max fpre.length pre₂.length + max fsuf.length suf₂.length) (by omega)
                obtain ⟨us, hus⟩ :=
                  rowOfG_total (pre := pre₂) (suf := suf₂) (c := c)
                    (n := max fpre.length pre₂.length + max fsuf.length suf₂.length) (by omega)
                rw [hfs, hus] at h
                cases hfc : f c with
                | none => rw [hfc] at h; exact absurd h (by simp)
                | some spz =>
                    rw [hfc] at h
                    obtain ⟨row, hrow, rfl⟩ := Option.map_eq_some_iff.mp h
                    have hfsl : fs.length
                        = max fpre.length pre₂.length + max fsuf.length suf₂.length :=
                      rowOfG_length hfs
                    have husl : us.length
                        = max fpre.length pre₂.length + max fsuf.length suf₂.length :=
                      rowOfG_length hus
                    have hFz : List.Forall₂
                        (fun (p : (Term → Option Term) × Term) w => p.1 p.2 = some w)
                        (fs.zip us) row :=
                      allSome_map_forall₂ _ (by rw [← zipF_eq]; exact hrow)
                    have hrowlen : row.length
                        = max fpre.length pre₂.length + max fsuf.length suf₂.length := by
                      have hz := hFz.length_eq
                      simp only [List.length_zip, hfsl, husl] at hz
                      omega
                    have htk : (row.take (max fpre.length pre₂.length)).length
                        = max fpre.length pre₂.length := by
                      rw [List.length_take, hrowlen]; omega
                    have hdp : (row.drop (max fpre.length pre₂.length)).length
                        = max fsuf.length suf₂.length := by
                      rw [List.length_drop, hrowlen]; omega
                    obtain ⟨ts, hts, htsF⟩ :=
                      rowOfG_forall₂_left hp (Or.inr ⟨t, f, rfl, rfl, hsound⟩) hf hfs
                    have htsl : ts.length
                        = max fpre.length pre₂.length + max fsuf.length suf₂.length :=
                      rowOfG_length hts
                    have hrel₀ := zipF_lift_termsA htsF hFz
                    have hspz : AdmAAt t c spz := hsound c spz hfc
                    have hdm := dominates_max hdom
                    refine AdmAAt_listOf ?_
                    refine AdmA_list_at (p₁ := pre) (q₁ := some t) (s₁ := suf) ?_ ?_
                    · intro n
                      simp only [rowOfG_some_isSome, htk, hdp]
                      rcases Nat.lt_or_ge n (pre.length + suf.length) with h1 | h1
                      · rw [decide_eq_false (by omega : ¬ (max fpre.length pre₂.length
                          + max fsuf.length suf₂.length ≤ n)),
                          decide_eq_false (by omega : ¬ (pre.length + suf.length ≤ n)),
                          Bool.false_and]
                      · rcases Nat.lt_or_ge n (pre₂.length + suf₂.length) with h2 | h2
                        · rw [decide_eq_false (by omega : ¬ (max fpre.length pre₂.length
                            + max fsuf.length suf₂.length ≤ n)),
                            decide_eq_true (by omega : pre.length + suf.length ≤ n),
                            decide_eq_false (by omega : ¬ (pre₂.length + suf₂.length ≤ n)),
                            Bool.and_false]
                        · rw [decide_eq_true (by omega : max fpre.length pre₂.length
                            + max fsuf.length suf₂.length ≤ n),
                            decide_eq_true (by omega : pre.length + suf.length ≤ n),
                            decide_eq_true (by omega : pre₂.length + suf₂.length ≤ n),
                            Bool.and_self]
                    · intro n r₁ r₂ rz h1 h2 h3
                      rw [rowOfG_some_eq, htk, hdp] at h3
                      split at h3
                      · exact absurd h3 (by simp)
                      · next hge =>
                          simp only [Option.some.injEq] at h3
                          subst h3
                          have hr₁ := rowOfG_respread (P := max fpre.length pre₂.length)
                            (S := max fsuf.length suf₂.length)
                            (by omega) (by omega) (by omega) hts h1
                          have hr₂ := rowOfG_respread (P := max fpre.length pre₂.length)
                            (S := max fsuf.length suf₂.length)
                            (by omega) (by omega) (by omega) hus h2
                          subst hr₁; subst hr₂
                          refine ⟨?_, ?_⟩
                          · simp only [List.length_append, List.length_take, List.length_drop,
                              List.length_replicate, htsl, husl]
                          · refine forall₂_zip_append ?_
                              (forall₂_zip_append ?_ (forall₂_zip_take _ hrel₀)
                                (forall₂_zip_replicate hspz _))
                              (forall₂_zip_drop _ hrel₀)
                            · simp only [List.length_append, List.length_take,
                                List.length_replicate, htsl, husl]
                            · simp only [List.length_take, htsl, husl]
            · exact absurd h (by simp)
  case opaq => simp [famList] at h
  all_goals admA_never famList

/-- **A body reads a map by its slots**, the read side's twin of `AdmBody_map_slots`. -/
theorem AdmABody_map_slots (c : Body) (keys : Finset Name) (g : {k // k ∈ keys} → Attr) :
    AdmABody c (.m keys g) = true ↔
      (∀ k, ObjectSlot.isReq (c.slotAt k) = true → k ∈ keys) ∧
      ∀ k : {k // k ∈ keys}, AdmAField (c.slotAt k.1) (g k) = true := by
  rw [AdmABody_map, reqPresentT_req, Bool.and_eq_true, reqs_slotAt]
  apply and_congr Iff.rfl
  unfold objAdmA; rw [decide_eq_true_iff]
  refine forall_congr' fun k => ?_
  unfold entryPA; simp only [MapOf.at]
  rcases Decidable.em (k.1 ∈ c.fields) with hk | hk
  · rw [dif_pos hk, Body.slotAt_pos hk]
  · rw [dif_neg hk, Body.slotAt_neg hk]
    cases hw : c.wild with
    | none => simp [AdmAWild, Body.block, hw, AdmAField, AdmA]
    | some t => simp [AdmAWild, Body.block, hw, AdmAField]

/-- **Two bodies conjoined at every name are conjoined as bodies**, read side. -/
theorem AdmABody_of_slots {a b z : Body}
    (hS : ∀ k c, AdmAField (z.slotAt k) c = (AdmAField (a.slotAt k) c && AdmAField (b.slotAt k) c))
    (hR : ∀ k, ObjectSlot.isReq (z.slotAt k)
      = (ObjectSlot.isReq (a.slotAt k) || ObjectSlot.isReq (b.slotAt k)))
    (c : Attr) : AdmABody z c = (AdmABody a c && AdmABody b c) := by
  cases c
  case m keys g =>
    rw [Bool.eq_iff_iff, Bool.and_eq_true, AdmABody_map_slots, AdmABody_map_slots,
      AdmABody_map_slots]
    constructor
    · rintro ⟨hr, hs⟩
      refine ⟨⟨fun k h => hr k (by rw [hR, h, Bool.true_or]), fun k => ?_⟩,
        ⟨fun k h => hr k (by rw [hR, h, Bool.or_true]), fun k => ?_⟩⟩
      · have h1 := hs k; rw [hS, Bool.and_eq_true] at h1; exact h1.1
      · have h1 := hs k; rw [hS, Bool.and_eq_true] at h1; exact h1.2
    · rintro ⟨⟨hra, hsa⟩, ⟨hrb, hsb⟩⟩
      refine ⟨fun k h => ?_, fun k => by rw [hS, hsa k, hsb k]; rfl⟩
      rw [hR, Bool.or_eq_true] at h
      exact h.elim (hra k) (hrb k)
  all_goals
    rw [AdmABody_of_not_m (fun _ _ hc => Attr.noConfusion hc),
      AdmABody_of_not_m (fun _ _ hc => Attr.noConfusion hc),
      AdmABody_of_not_m (fun _ _ hc => Attr.noConfusion hc)]; rfl

/-- A present name reads through its slot's codec, the block `never` standing in for a
    closed body: `Codec.empty` reads nothing, and neither does a missing rest codec. -/
theorem entryCodec_slotAt (c : Body) (k : Name) (x : Attr) :
    (entryCodec ⟨c.fields, fun k => fieldSem (c.at k)⟩ (rcOf (wildSem c.wild)) k).bind
        (fun cd => cd.p x)
      = (fieldSem (c.slotAt k)).codec.p x := by
  unfold entryCodec; simp only [MapOf.at]
  rcases Decidable.em (k ∈ c.fields) with hk | hk
  · rw [dif_pos hk, Body.slotAt_pos hk]; rfl
  · rw [dif_neg hk, Body.slotAt_neg hk]
    cases hw : c.wild with
    | none => simp [wildSem, rcOf, Body.block, hw, fieldSem, FieldSem.codec, denote, Codec.empty]
    | some t => simp [wildSem, rcOf, Body.block, hw, fieldSem, FieldSem.codec]

/-- **Two bodies that read every present name alike read the map alike.** -/
theorem bodySem_p_congr {c d : Body} {keys : Finset Name} {g : {k // k ∈ keys} → Attr}
    (hc : reqPresentB ⟨c.fields, fun k => fieldSem (c.at k)⟩ keys = true)
    (hd : reqPresentB ⟨d.fields, fun k => fieldSem (d.at k)⟩ keys = true)
    (he : ∀ k (hk : k ∈ keys), (fieldSem (c.slotAt k)).codec.p (g ⟨k, hk⟩)
      = (fieldSem (d.slotAt k)).codec.p (g ⟨k, hk⟩)) :
    (bodySem c).p (.m keys g) = (bodySem d).p (.m keys g) := by
  have hkc : ∀ w : Option Term, ∀ sems : MapOf FieldSem,
      keepB (wildSem w) sems = fun _ => true := by
    intro w sems; cases w <;> rfl
  cases c with
  | mk fc Fc wc =>
    cases d with
    | mk fd Fd wd =>
      simp only [bodySem, objectCodec, objectCodecCore, carriedCodec, mapV, mA, hkc, Option.bind_some]
      simp only [objRead]
      simp only [Body.fields_mk, Body.at_mk] at hc hd
      rw [if_pos hc, if_pos hd, Option.map_map, Option.map_map]
      apply funImage_record_congr
      · rfl
      · intro k hk _
        have hk' := (Finset.mem_filter.mp hk).1
        have h1 := entryCodec_slotAt (.mk fc Fc wc) k (g ⟨k, hk'⟩)
        have h2 := entryCodec_slotAt (.mk fd Fd wd) k (g ⟨k, hk'⟩)
        simp only [Body.fields_mk, Body.at_mk, Body.wild_mk] at h1 h2
        exact (h1.trans (he k hk')).trans h2.symm

/-- A body that reads a map finds every required name present. -/
theorem reqPresentB_of_AdmABody {c : Body} {keys : Finset Name} {g : {k // k ∈ keys} → Attr}
    (h : AdmABody c (.m keys g) = true) :
    reqPresentB ⟨c.fields, fun k => fieldSem (c.at k)⟩ keys = true := by
  rw [AdmABody_map, Bool.and_eq_true] at h
  rw [← reqPresentT_eq]; exact h.1

/-- **Two objects conjoined at every name, read side**: the rows conjoin, and where both
    factors read a map the meet reads it as each of them does. -/
theorem AdmA_object_of_slots {a b z : Body}
    (hS : ∀ k c, AdmAField (z.slotAt k) c = (AdmAField (a.slotAt k) c && AdmAField (b.slotAt k) c))
    (hR : ∀ k, ObjectSlot.isReq (z.slotAt k)
      = (ObjectSlot.isReq (a.slotAt k) || ObjectSlot.isReq (b.slotAt k)))
    (hP : ∀ k c, AdmAField (a.slotAt k) c = true → AdmAField (b.slotAt k) c = true →
      (fieldSem (z.slotAt k)).codec.p c = (fieldSem (a.slotAt k)).codec.p c
        ∧ (fieldSem (z.slotAt k)).codec.p c = (fieldSem (b.slotAt k)).codec.p c) :
    (∀ c, AdmA (.object z) c = (AdmA (.object a) c && AdmA (.object b) c)) ∧
    (∀ c, AdmA (.object a) c = true → AdmA (.object b) c = true →
      (denote (.object z)).p c = (denote (.object a)).p c
        ∧ (denote (.object z)).p c = (denote (.object b)).p c) := by
  have half1 : ∀ c, AdmA (.object z) c = (AdmA (.object a) c && AdmA (.object b) c) :=
    AdmABody_of_slots hS hR
  refine ⟨half1, fun c hA hB => ?_⟩
  have hZ : AdmA (.object z) c = true := by rw [half1, hA, hB]; rfl
  cases c
  case m keys g =>
    have hA' : AdmABody a (.m keys g) = true := hA
    have hB' : AdmABody b (.m keys g) = true := hB
    have hZ' : AdmABody z (.m keys g) = true := hZ
    have hsa := ((AdmABody_map_slots a keys g).mp hA').2
    have hsb := ((AdmABody_map_slots b keys g).mp hB').2
    refine ⟨bodySem_p_congr (reqPresentB_of_AdmABody hZ') (reqPresentB_of_AdmABody hA')
        (fun k hk => (hP k _ (hsa ⟨k, hk⟩) (hsb ⟨k, hk⟩)).1),
      bodySem_p_congr (reqPresentB_of_AdmABody hZ') (reqPresentB_of_AdmABody hB')
        (fun k hk => (hP k _ (hsa ⟨k, hk⟩) (hsb ⟨k, hk⟩)).2)⟩
  all_goals exact absurd hA (by
    show ¬ AdmABody a _ = true
    rw [AdmABody_of_not_m (fun _ _ hc => Attr.noConfusion hc)]; simp)

/-- **A slot at the bottom empties the product, read side.** -/
theorem AdmABody_false_of_bottom {a b : Body} {s : ObjectSlot} {k : Name}
    (hs : ∀ c, AdmAField s c = (AdmAField (a.slotAt k) c && AdmAField (b.slotAt k) c))
    (hr : ObjectSlot.isReq s = (ObjectSlot.isReq (a.slotAt k) || ObjectSlot.isReq (b.slotAt k)))
    (hbot : ObjectSlot.isBottom s = true) (c : Attr) :
    (AdmABody a c && AdmABody b c) = false := by
  refine Bool.eq_false_iff.mpr (fun hab => ?_)
  rw [Bool.and_eq_true] at hab
  obtain ⟨hA, hB⟩ := hab
  cases c
  case m keys g =>
    rw [AdmABody_map_slots] at hA hB
    have hreq := isReq_of_isBottom hbot
    rw [hr, Bool.or_eq_true] at hreq
    have hk : k ∈ keys := hreq.elim (hA.1 k) (hB.1 k)
    have h1 := hs (g ⟨k, hk⟩)
    rw [hA.2 ⟨k, hk⟩, hB.2 ⟨k, hk⟩] at h1
    cases s with
    | req t =>
      have ht : t = .never := by
        cases t <;> simp_all [ObjectSlot.isBottom, Term.isNever]
      subst ht; exact absurd h1 (by simp [AdmAField, AdmA])
    | optional t => exact absurd hbot (by simp [ObjectSlot.isBottom])
  all_goals exact absurd hA (by rw [AdmABody_of_not_m (fun _ _ hc => Attr.noConfusion hc)]; simp)

/-- **One name of the met body, on the read side**: the slot reads exactly what both bodies'
    slots at that name read, is required where either is, and reads a stored attribute both
    admit as each of them does. -/
theorem objSlot_soundA {a b : Body} {g : {k // k ∈ a.fields} → ObjectSlot → Option ObjectSlot}
    {mw : Term → Option Term}
    (hg : ∀ (k : {k // k ∈ a.fields}) (fl fm : ObjectSlot), g k fl = some fm →
      (∀ c, AdmAField fm c = (AdmAField (a.at k) c && AdmAField fl c))
      ∧ (∀ c, AdmAField (a.at k) c = true → AdmAField fl c = true →
          (fieldSem fm).codec.p c = (fieldSem (a.at k)).codec.p c
            ∧ (fieldSem fm).codec.p c = (fieldSem fl).codec.p c))
    (hgreq : ∀ (k : {k // k ∈ a.fields}) (fl fm : ObjectSlot), g k fl = some fm →
      ObjectSlot.isReq fm = (ObjectSlot.isReq (a.at k) || ObjectSlot.isReq fl))
    (hw : ∀ y z, mw y = some z → AdmAAt a.block y z)
    {k : {k // k ∈ a.fields ∪ b.fields}} {s : ObjectSlot} (h : objSlot a b g mw k = some s) :
    (∀ c, AdmAField s c = (AdmAField (a.slotAt k.1) c && AdmAField (b.slotAt k.1) c)) ∧
    ObjectSlot.isReq s = (ObjectSlot.isReq (a.slotAt k.1) || ObjectSlot.isReq (b.slotAt k.1)) ∧
    (∀ c, AdmAField (a.slotAt k.1) c = true → AdmAField (b.slotAt k.1) c = true →
      (fieldSem s).codec.p c = (fieldSem (a.slotAt k.1)).codec.p c
        ∧ (fieldSem s).codec.p c = (fieldSem (b.slotAt k.1)).codec.p c) := by
  unfold objSlot at h
  split at h
  next ha =>
    have hb : (if h' : k.1 ∈ b.fields then b.at ⟨k.1, h'⟩ else .optional b.block)
        = b.slotAt k.1 := rfl
    rw [hb] at h
    rw [Body.slotAt_pos ha]
    exact ⟨(hg _ _ _ h).1, hgreq _ _ _ h, (hg _ _ _ h).2⟩
  next ha =>
    have hb := (Finset.mem_union.mp k.2).resolve_left ha
    rw [Body.slotAt_neg ha, Body.slotAt_pos hb]
    cases hf : b.at ⟨k.1, hb⟩ with
    | req y =>
      rw [hf] at h
      simp only [ObjectSlot.through, Option.map_eq_some_iff] at h
      obtain ⟨z, hz, rfl⟩ := h
      exact ⟨fun c => (hw _ _ hz).1 c, rfl, fun c h1 h2 => (hw _ _ hz).2 c h1 h2⟩
    | optional y =>
      rw [hf] at h
      simp only [ObjectSlot.through, Option.map_eq_some_iff] at h
      obtain ⟨z, hz, rfl⟩ := h
      exact ⟨fun c => (hw _ _ hz).1 c, rfl, fun c h1 h2 => (hw _ _ hz).2 c h1 h2⟩

/-- **Two objects meet pointwise, and the meet is exact on the read side.** -/
theorem admA_famObj {a : Body} {g : {k // k ∈ a.fields} → ObjectSlot → Option ObjectSlot}
    {mw : Term → Option Term}
    (hg : ∀ (k : {k // k ∈ a.fields}) (fl fm : ObjectSlot), g k fl = some fm →
      (∀ c, AdmAField fm c = (AdmAField (a.at k) c && AdmAField fl c))
      ∧ (∀ c, AdmAField (a.at k) c = true → AdmAField fl c = true →
          (fieldSem fm).codec.p c = (fieldSem (a.at k)).codec.p c
            ∧ (fieldSem fm).codec.p c = (fieldSem fl).codec.p c))
    (hgreq : ∀ (k : {k // k ∈ a.fields}) (fl fm : ObjectSlot), g k fl = some fm →
      ObjectSlot.isReq fm = (ObjectSlot.isReq (a.at k) || ObjectSlot.isReq fl))
    (hw : ∀ y z, mw y = some z → AdmAAt a.block y z) :
    AdmAFam (.object a) (famObj a g mw) := by
  intro y z hd h
  cases y <;> first | exact hd.elim | skip
  case object b =>
      simp only [famObj] at h
      unfold objObj at h
      split at h
      next hbot =>
        obtain ⟨k, hk⟩ := of_decide_eq_true hbot
        obtain ⟨s, hs, hsb⟩ := Option.map_eq_some_iff.mp hk
        simp only [Option.some.injEq] at h; subst h
        obtain ⟨hS, hR, -⟩ := objSlot_soundA hg hgreq hw hs
        have hf := AdmABody_false_of_bottom hS hR hsb
        refine ⟨fun c => (hf c).symm, fun c hA hB => ?_⟩
        have hA' : AdmABody a c = true := hA
        have hB' : AdmABody b c = true := hB
        have := hf c
        rw [hA', hB'] at this; exact absurd this (by simp)
      next =>
        split at h
        next => exact absurd h (by simp)
        next zb hwz =>
          split at h
          next hall =>
            simp only [Option.some.injEq] at h; subst h
            have hbw := hw _ _ hwz
            have hblk : ∀ k, k ∉ a.fields → k ∉ b.fields →
                (∀ c, AdmAField (.optional (if zb.isNever then .never else zb)) c
                  = (AdmAField (a.slotAt k) c && AdmAField (b.slotAt k) c)) ∧
                ObjectSlot.isReq (.optional (if zb.isNever then .never else zb))
                  = (ObjectSlot.isReq (a.slotAt k) || ObjectSlot.isReq (b.slotAt k)) ∧
                (∀ c, AdmAField (a.slotAt k) c = true → AdmAField (b.slotAt k) c = true →
                  (fieldSem (.optional (if zb.isNever then .never else zb))).codec.p c
                    = (fieldSem (a.slotAt k)).codec.p c
                  ∧ (fieldSem (.optional (if zb.isNever then .never else zb))).codec.p c
                    = (fieldSem (b.slotAt k)).codec.p c) := by
              intro k ha hb
              rw [Body.slotAt_neg ha, Body.slotAt_neg hb]
              cases hn : zb.isNever
              · exact ⟨fun c => hbw.1 c, rfl, fun c h1 h2 => hbw.2 c h1 h2⟩
              · rw [if_pos rfl]
                have hz := eq_never_of_isNever hn
                subst hz
                exact ⟨fun c => hbw.1 c, rfl, fun c h1 h2 => hbw.2 c h1 h2⟩
            have hall' := of_decide_eq_true hall
            refine AdmA_object_of_slots (fun k c => ?_) (fun k => ?_) (fun k c => ?_)
            · exact objObj_slots (P := fun k s => AdmAField s c
                  = (AdmAField (a.slotAt k) c && AdmAField (b.slotAt k) c)) hall'
                (fun k' s hs => (objSlot_soundA hg hgreq hw hs).1 c)
                (fun k' ha hb => (hblk k' ha hb).1 c) k
            · exact objObj_slots (P := fun k s => ObjectSlot.isReq s
                  = (ObjectSlot.isReq (a.slotAt k) || ObjectSlot.isReq (b.slotAt k))) hall'
                (fun k' s hs => (objSlot_soundA hg hgreq hw hs).2.1)
                (fun k' ha hb => (hblk k' ha hb).2.1) k
            · exact objObj_slots (P := fun k s => AdmAField (a.slotAt k) c = true →
                  AdmAField (b.slotAt k) c = true →
                  (fieldSem s).codec.p c = (fieldSem (a.slotAt k)).codec.p c
                    ∧ (fieldSem s).codec.p c = (fieldSem (b.slotAt k)).codec.p c) hall'
                (fun k' s hs => (objSlot_soundA hg hgreq hw hs).2.2 c)
                (fun k' ha hb => (hblk k' ha hb).2.2 c) k
          next => exact absurd h (by simp)
  case opaq => simp [famObj] at h
  all_goals admA_never famObj

mutual
/-- **The read side's homomorphism and its reading agreement, together.** Both halves are
    proved at once because a refinement row needs the agreement against whichever factor the
    wrapper sits on. -/
theorem AdmA_meet_both : ∀ x y z, Term.meet x y = some z → AdmAAt x y z
  | .never, _, _, h => by
      simp only [Term.meet, Option.some.injEq] at h; subst h
      exact ⟨fun a => rfl, fun a ha _ => absurd ha (by simp [AdmA])⟩
  | .held _ _ _ _, y, _, h => by
      cases y <;>
        first
          | (simp only [Term.meet, Option.some.injEq] at h; subst h
             exact ⟨fun a => by simp [AdmA], fun a _ hb => absurd hb (by simp [AdmA])⟩)
          | exact absurd h (by simp [Term.meet])
  | .lazy x, y, _, h => by
      rw [Term.meet] at h
      obtain ⟨ih1, ih2⟩ := AdmA_meet_both x y _ h
      exact ⟨fun a => by simpa [AdmA] using ih1 a,
        fun a ha hb => ih2 a (by simpa [AdmA] using ha) hb⟩
  | .refine x p, y, _, h => by
      cases y with
      | never =>
          simp only [Term.meet, Option.some.injEq] at h; subst h
          exact ⟨fun a => by simp [AdmA], fun a _ hb => absurd hb (by simp [AdmA])⟩
      | _ =>
        simp only [Term.meet] at h
        split at h
        · obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨ih1, ih2⟩ := AdmA_meet_both x _ w hw
          exact refine_row_l ih1 ih2
        · exact absurd h (by simp)
  | .union os, y, _, h => by
      cases y with
      | never =>
          simp only [Term.meet, Option.some.injEq] at h; subst h
          exact ⟨fun a => by simp [AdmA], fun a _ hb => absurd hb (by simp [AdmA])⟩
      | _ =>
        obtain ⟨zs, hF, rfl⟩ := meet_union_of h (by simp)
        have hB := admA_meetL os _ zs hF
        refine ⟨fun a => ?_, fun a ha hb => ?_⟩
        · exact union_meet_freeA a (List.Forall₂.imp (fun _ _ hh => hh.1) hB)
        · obtain ⟨t, hft⟩ := find?_of_AdmA_union ha
          have hta : AdmA t a = true := List.find?_some (p := fun u => AdmA u a) hft
          obtain ⟨w, hfw, hwA, hwP⟩ :=
            find?_forall₂ (q := fun u => AdmA u a) (fun _ _ hh => by rw [hh.1 a, hb, Bool.and_true])
              hB hft
          rw [ofOptions_p_find, find?_filter_of (fun w hw => by rw [not_isNever_of_admA hw]; rfl),
            hfw, union_p_find, hft]
          exact hwP a hta hb
  | .string, y, z, h => admA_meetSRight admA_famString y z h
  | .number, y, z, h => admA_meetSRight admA_famNumber y z h
  | .boolean, y, z, h => admA_meetSRight admA_famBoolean y z h
  | .binary, y, z, h => admA_meetSRight admA_famBinary y z h
  | .null, y, z, h => admA_meetSRight admA_famNull y z h
  | .literal k lv, y, z, h => admA_meetSRight (admA_famLit k lv) y z h
  | .set b, y, z, h => admA_meetSRight (admA_famSet b) y z h
  | .opaq, y, z, h => admA_meetSRight (admA_famOpaq) y z h
  | .list pre sp suf, y, z, h => by
      cases sp with
      | none =>
          exact admA_meetSRight (admA_famList (pre := pre) (sp := none) (suf := suf)
            (admA_meetSTs pre) (Or.inl ⟨rfl, rfl⟩) (admA_meetSTs suf)) y z h
      | some t =>
          exact admA_meetSRight (admA_famList (pre := pre) (sp := some t) (suf := suf)
            (admA_meetSTs pre)
            (Or.inr ⟨t, Term.meet t, rfl, rfl, fun u w hw => AdmA_meet_both t u w hw⟩)
            (admA_meetSTs suf)) y z h
  | .object (.mk fs f none), y, z, h =>
      admA_meetSRight (admA_famObj (a := .mk fs f none)
        (fun k fl fm hm => admA_Field_meet (f k) fl fm hm)
        (fun _ _ _ hm => isReq_Field_meet hm)
        (fun _ _ hz => by
          simp only [Option.some.injEq] at hz; subst hz
          exact ⟨fun _ => rfl, fun _ ha _ => absurd ha (by simp [Body.block, AdmA])⟩)) y z h
  | .object (.mk fs f (some t)), y, z, h =>
      admA_meetSRight (admA_famObj (a := .mk fs f (some t))
        (fun k fl fm hm => admA_Field_meet (f k) fl fm hm)
        (fun _ _ _ hm => isReq_Field_meet hm)
        (fun u w hw => AdmA_meet_both t u w hw)) y z h
termination_by structural x => x

/-- The union row's options, lifted pointwise at the fixed partner. -/
theorem admA_meetL : ∀ (os : List Term) (y : Term) (zs : List Term),
    List.Forall₂ (fun t w => Term.meet t y = some w) os zs →
    List.Forall₂ (fun t w =>
      (∀ b, AdmA w b = (AdmA t b && AdmA y b)) ∧
      (∀ b, AdmA t b = true → AdmA y b = true →
        (denote w).p b = (denote t).p b ∧ (denote w).p b = (denote y).p b)) os zs
  | [], _, _, h => by cases h; exact .nil
  | t :: ts, y, _, h => by
      cases h with
      | cons hh ht => exact .cons (AdmA_meet_both t y _ hh) (admA_meetL ts y _ ht)
termination_by structural os => os

/-- Every position of a tuple carries the meet at that position. -/
theorem admA_meetSTs : ∀ ts : List Term, List.Forall₂ AdmASound ts (Term.meetSTs ts)
  | [] => .nil
  | t :: ts => .cons (fun u w hw => AdmA_meet_both t u w hw) (admA_meetSTs ts)
termination_by structural ts => ts

/-- Two fields at one name read what both read, and read it to the same value. -/
theorem admA_Field_meet : ∀ (f fl : ObjectSlot) (fm : ObjectSlot), ObjectSlot.meet f fl = some fm →
    (∀ c, AdmAField fm c = (AdmAField f c && AdmAField fl c))
    ∧ (∀ c, AdmAField f c = true → AdmAField fl c = true →
        (fieldSem fm).codec.p c = (fieldSem f).codec.p c
          ∧ (fieldSem fm).codec.p c = (fieldSem fl).codec.p c)
  | .req x, .req y, _, h => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h; exact AdmA_meet_both x y tz hz
  | .req x, .optional y, _, h => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h; exact AdmA_meet_both x y tz hz
  | .optional x, .req y, _, h => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h; exact AdmA_meet_both x y tz hz
  | .optional x, .optional y, _, h => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h; exact AdmA_meet_both x y tz hz
termination_by structural f => f
end


/-- **`AdmA` is a homomorphism from the meet to conjunction.** Where two terms have a meet, the
    attributes it reads are exactly the attributes both read. -/
theorem AdmA_meet {x y z : Term} (h : Term.meet x y = some z) (a : Attr) :
    AdmA z a = (AdmA x a && AdmA y a) :=
  (AdmA_meet_both x y z h).1 a

/-- **…and it reads them to the same value.** The read agreement is proved with the homomorphism
    and not after it: `AdmA (.refine t p) a` asks the predicate of what `t` decodes `a` to. -/
theorem denote_meet_p {x y z : Term} (h : Term.meet x y = some z) {a : Attr}
    (hx : AdmA x a = true) (hy : AdmA y a = true) :
    (denote z).p a = (denote x).p a ∧ (denote z).p a = (denote y).p a :=
  (AdmA_meet_both x y z h).2 a hx hy

end StructuralAdmA


/-! ## The bottom, and what a sub-selection keeps -/

/-- The bottom admits no value. -/
theorem Adm_never (v : Value) : Adm .never v = false := rfl

/-- …and reads no attribute. -/
theorem AdmA_never (a : Attr) : AdmA .never a = false := rfl

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

/-- A row that admits at least what another row admits. -/
def RowLe {α : Type} (P Q : α → Bool) : Prop := ∀ x, P x = true → Q x = true

/-- The fixed positions and the spread of a list admit more when each row admits more. -/
theorem alignP_mono {Ps Qs : List VP} {sp sq : Option VP} (hPQ : List.Forall₂ RowLe Ps Qs)
    (hs : Option.Rel RowLe sp sq) : ∀ vs, alignP Ps sp vs = true → alignP Qs sq vs = true := by
  induction hPQ with
  | nil =>
    cases hs with
    | none => exact fun _ h => h
    | some hr =>
      intro vs h
      induction vs with
      | nil => rfl
      | cons v vs ih =>
        simp only [alignP, Bool.and_eq_true] at h ⊢
        exact ⟨hr _ h.1, ih h.2⟩
  | cons hr _ ih =>
    intro vs h
    cases vs with
    | nil => simp [alignP] at h
    | cons v vs =>
      simp only [alignP, Bool.and_eq_true] at h ⊢
      exact ⟨hr _ h.1, ih vs h.2⟩

/-- The suffix of a list admits more when each row admits more. -/
theorem zipP_mono {Ps Qs : List VP} (hPQ : List.Forall₂ RowLe Ps Qs) :
    ∀ vs, zipP Ps vs = true → zipP Qs vs = true := by
  induction hPQ with
  | nil => exact fun _ h => h
  | cons hr _ ih =>
    intro vs h
    cases vs with
    | nil => simp [zipP] at h
    | cons v vs =>
      simp only [zipP, Bool.and_eq_true] at h ⊢
      exact ⟨hr _ h.1, ih vs h.2⟩

/-- A list admits more when each row admits more. -/
theorem alignPL_mono {Ps Qs Ss Ts : List VP} {sp sq : Option VP}
    (hPQ : List.Forall₂ RowLe Ps Qs) (hs : Option.Rel RowLe sp sq)
    (hST : List.Forall₂ RowLe Ss Ts) (vs : List Value) (h : alignPL Ps sp Ss vs = true) :
    alignPL Qs sq Ts vs = true := by
  unfold alignPL at h ⊢
  rw [← hST.length_eq]
  simp only [Bool.and_eq_true] at h ⊢
  exact ⟨alignP_mono hPQ hs _ h.1, zipP_mono hST _ h.2⟩

/-- The fixed positions and the spread of a stored list read more when each row reads more. -/
theorem alignPA_mono {Ps Qs : List AP} {sp sq : Option AP} (hPQ : List.Forall₂ RowLe Ps Qs)
    (hs : Option.Rel RowLe sp sq) : ∀ as, alignPA Ps sp as = true → alignPA Qs sq as = true := by
  induction hPQ with
  | nil =>
    cases hs with
    | none => exact fun _ h => h
    | some hr =>
      intro as h
      induction as with
      | nil => rfl
      | cons a as ih =>
        simp only [alignPA, Bool.and_eq_true] at h ⊢
        exact ⟨hr _ h.1, ih h.2⟩
  | cons hr _ ih =>
    intro as h
    cases as with
    | nil => simp [alignPA] at h
    | cons a as =>
      simp only [alignPA, Bool.and_eq_true] at h ⊢
      exact ⟨hr _ h.1, ih as h.2⟩

/-- The suffix of a stored list reads more when each row reads more. -/
theorem zipPA_mono {Ps Qs : List AP} (hPQ : List.Forall₂ RowLe Ps Qs) :
    ∀ as, zipPA Ps as = true → zipPA Qs as = true := by
  induction hPQ with
  | nil => exact fun _ h => h
  | cons hr _ ih =>
    intro as h
    cases as with
    | nil => simp [zipPA] at h
    | cons a as =>
      simp only [zipPA, Bool.and_eq_true] at h ⊢
      exact ⟨hr _ h.1, ih as h.2⟩

/-- A stored list reads more when each row reads more. -/
theorem alignPAL_mono {Ps Qs Ss Ts : List AP} {sp sq : Option AP}
    (hPQ : List.Forall₂ RowLe Ps Qs) (hs : Option.Rel RowLe sp sq)
    (hST : List.Forall₂ RowLe Ss Ts) (as : List Attr) (h : alignPAL Ps sp Ss as = true) :
    alignPAL Qs sq Ts as = true := by
  unfold alignPAL at h ⊢
  rw [← hST.length_eq]
  simp only [Bool.and_eq_true] at h ⊢
  exact ⟨alignPA_mono hPQ hs _ h.1, zipPA_mono hST _ h.2⟩

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
  | _ => exact absurd h (by simp [Adm])

/-- A list whose positions have `ReadLe` has `ReadLe`. -/
theorem readLe_list {pre suf : List Term} {sp : Option Term} (hp : ReadLeL pre)
    (hs : ReadLeO sp) (hf : ReadLeL suf) : ReadLe (.list pre sp suf) := by
  intro a h
  cases a with
  | l as =>
    exact alignPAL_mono (readLeL_forall₂ pre hp) (readLeO_rel sp hs)
      (readLeL_forall₂ suf hf) as h
  | _ => exact absurd h (by simp [AdmA])

/-- An object whose slots and open block have `WriteLe` has `WriteLe`. The view keeps each
    presence mark, so the presence test does not move. -/
theorem writeLe_object {fs : Finset Name} {f : {k // k ∈ fs} → ObjectSlot} {w : Option Term}
    (hf : ∀ k, RowLe (AdmField (f k)) (AdmField (writeViewS (f k)))) (hw : WriteLeO w) :
    WriteLe (.object (.mk fs f w)) := by
  intro v h
  cases v with
  | map keys g =>
    simp only [writeView, writeViewB, Adm, AdmBody, Bool.and_eq_true] at h ⊢
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
        | none => exact absurd this (by simp [AdmWild])
        | some t => exact hw _ this
  | _ => exact absurd h (by simp [Adm, AdmBody])

/-- An object whose slots and open block have `ReadLe` has `ReadLe`. -/
theorem readLe_object {fs : Finset Name} {f : {k // k ∈ fs} → ObjectSlot} {w : Option Term}
    (hf : ∀ k, RowLe (AdmAField (f k)) (AdmAField (readViewS (f k)))) (hw : ReadLeO w) :
    ReadLe (.object (.mk fs f w)) := by
  intro a h
  cases a with
  | m keys g =>
    simp only [readView, readViewB, AdmA, AdmABody, Bool.and_eq_true] at h ⊢
    refine ⟨decide_eq_true fun k => ?_, decide_eq_true fun k => ?_⟩
    · have := of_decide_eq_true h.1 k
      beta_reduce
      generalize f k = s at this ⊢
      cases s <;> simp_all [readViewS]
    · have := of_decide_eq_true h.2 k
      rcases Decidable.em (k.1 ∈ fs) with hm | hm
      · simp only [entryPA, MapOf.at, dif_pos hm] at this ⊢
        exact hf ⟨k.1, hm⟩ _ this
      · simp only [entryPA, MapOf.at, dif_neg hm] at this ⊢
        cases w with
        | none => exact absurd this (by simp [AdmAWild])
        | some t => exact hw _ this
  | _ => exact absurd h (by simp [AdmA, AdmABody])

mutual
/-- **The caller-side view admits each value that the term admits**, where no `held` occurs
    below a `union`. A `union` stays as written, because a count selector is anti-monotone: two
    views can admit a value that one option alone admitted. -/
theorem writeLe_of : ∀ t : Term, heldBelowUnion t = false → WriteLe t
  | .held _ P _ _, hb => fun v h => by
      simp only [heldBelowUnion, Bool.or_eq_false_iff] at hb
      simp only [writeView]
      exact writeLe_of P hb.2 v (Bool.and_eq_true_iff.mp h).2
  | .refine t p, hb => fun v h => by
      simp only [heldBelowUnion] at hb
      simp only [writeView, Adm, Bool.and_eq_true] at h ⊢
      exact ⟨writeLe_of t hb v h.1, h.2⟩
  | .lazy t, hb => fun v h => by
      simp only [heldBelowUnion] at hb
      simp only [writeView]
      exact writeLe_of t hb v h
  | .list pre sp suf, hb => by
      simp only [heldBelowUnion, Bool.or_eq_false_iff] at hb
      exact writeLe_list (writeLe_ofL pre hb.1.1) (writeLe_ofO sp hb.1.2) (writeLe_ofL suf hb.2)
  | .object (.mk fs f w), hb => by
      simp only [heldBelowUnion, heldBelowUnionB, Bool.or_eq_false_iff,
        decide_eq_false_iff_not, not_exists, Bool.not_eq_true] at hb
      exact writeLe_object (fun k => writeLe_ofS (f k) (hb.1 k)) (writeLe_ofO w hb.2)
  | .union _, _ => fun _ h => h
  | .string, _ => fun _ h => h | .number, _ => fun _ h => h | .boolean, _ => fun _ h => h
  | .binary, _ => fun _ h => h | .null, _ => fun _ h => h | .literal _ _, _ => fun _ h => h
  | .set _, _ => fun _ h => h | .opaq, _ => fun _ h => h | .never, _ => fun _ h => h
/-- `writeLe_of` over a list. -/
theorem writeLe_ofL : ∀ ts : List Term, heldBelowUnionL ts = false → WriteLeL ts
  | [], _ => trivial
  | t :: ts, hb => by
      simp only [heldBelowUnionL, Bool.or_eq_false_iff] at hb
      exact ⟨writeLe_of t hb.1, writeLe_ofL ts hb.2⟩
/-- `writeLe_of` at an optional term. -/
theorem writeLe_ofO : ∀ o : Option Term, heldBelowUnionO o = false → WriteLeO o
  | none, _ => trivial
  | some t, hb => writeLe_of t hb
/-- `writeLe_of` at a slot. -/
theorem writeLe_ofS : ∀ s : ObjectSlot, heldBelowUnionS s = false →
    RowLe (AdmField s) (AdmField (writeViewS s))
  | .req t, hb => fun v h => writeLe_of t hb v h
  | .optional t, hb => fun v h => writeLe_of t hb v h
end

mutual
/-- **The stored-side view reads each attribute that the term reads**, where no `held` occurs
    below a `union`. -/
theorem readLe_of : ∀ t : Term, heldBelowUnion t = false → ReadLe t
  | .held t _ _ _, hb => fun a h => by
      simp only [heldBelowUnion, Bool.or_eq_false_iff] at hb
      simp only [readView]
      exact readLe_of t hb.1 a (Bool.and_eq_true_iff.mp h).1
  | .refine t p, hb => fun a h => by
      simp only [heldBelowUnion] at hb
      simp only [readView]
      split
      · exact readLe_of t hb a (Bool.and_eq_true_iff.mp h).1
      · exact h
  | .lazy t, hb => fun a h => by
      simp only [heldBelowUnion] at hb
      simp only [readView]
      exact readLe_of t hb a h
  | .list pre sp suf, hb => by
      simp only [heldBelowUnion, Bool.or_eq_false_iff] at hb
      exact readLe_list (readLe_ofL pre hb.1.1) (readLe_ofO sp hb.1.2) (readLe_ofL suf hb.2)
  | .object (.mk fs f w), hb => by
      simp only [heldBelowUnion, heldBelowUnionB, Bool.or_eq_false_iff,
        decide_eq_false_iff_not, not_exists, Bool.not_eq_true] at hb
      exact readLe_object (fun k => readLe_ofS (f k) (hb.1 k)) (readLe_ofO w hb.2)
  | .union _, _ => fun _ h => h
  | .string, _ => fun _ h => h | .number, _ => fun _ h => h | .boolean, _ => fun _ h => h
  | .binary, _ => fun _ h => h | .null, _ => fun _ h => h | .literal _ _, _ => fun _ h => h
  | .set _, _ => fun _ h => h | .opaq, _ => fun _ h => h | .never, _ => fun _ h => h
/-- `readLe_of` over a list. -/
theorem readLe_ofL : ∀ ts : List Term, heldBelowUnionL ts = false → ReadLeL ts
  | [], _ => trivial
  | t :: ts, hb => by
      simp only [heldBelowUnionL, Bool.or_eq_false_iff] at hb
      exact ⟨readLe_of t hb.1, readLe_ofL ts hb.2⟩
/-- `readLe_of` at an optional term. -/
theorem readLe_ofO : ∀ o : Option Term, heldBelowUnionO o = false → ReadLeO o
  | none, _ => trivial
  | some t, hb => readLe_of t hb
/-- `readLe_of` at a slot. -/
theorem readLe_ofS : ∀ s : ObjectSlot, heldBelowUnionS s = false →
    RowLe (AdmAField s) (AdmAField (readViewS s))
  | .req t, hb => fun a h => readLe_of t hb a h
  | .optional t, hb => fun a h => readLe_of t hb a h
end

/-- **The certificate through the views is sound.** A value that both terms admit is admitted
    by both caller-side views, and an attribute that both terms read is read by both stored-side
    views. The views are held-free, so `Orth` or the meet separates each pair of views. -/
theorem separates_of_certViews {x y : Term} (h : certViews x y = true) : Separates x y := by
  simp only [certViews, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨_, hbx⟩, hby⟩, hw⟩, hr⟩ := h
  have sw : Separates (writeView x) (writeView y) := by
    rcases Bool.or_eq_true_iff.mp hw with ho | hm
    · exact separates_of_orth ho
    · exact separates_of_meetNever hm
  have sr : Separates (readView x) (readView y) := by
    rcases Bool.or_eq_true_iff.mp hr with ho | hm
    · exact separates_of_orth ho
    · exact separates_of_meetNever hm
  refine ⟨fun v hx hy => ?_, fun a hx hy => ?_⟩
  · have hx' := writeLe_of x hbx v hx.2
    have hy' := writeLe_of y hby v hy.2
    exact sw.1 v ⟨occV_sound _ v hx', hx'⟩ ⟨occV_sound _ v hy', hy'⟩
  · have hx' := readLe_of x hbx a hx.2
    have hy' := readLe_of y hby a hy.2
    exact sr.2 a ⟨occA_sound _ a hx', hx'⟩ ⟨occA_sound _ a hy', hy'⟩

/-- **The pair certificate is sound**: each disjunct separates the pair. -/
theorem separates_of_certPair {x y : Term} (h : certPair x y = true) : Separates x y := by
  rcases Bool.or_eq_true_iff.mp h with h | hv
  · rcases Bool.or_eq_true_iff.mp h with ho | hm
    · exact separates_of_orth ho
    · exact separates_of_meetNever hm
  · exact separates_of_certViews hv

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

/-- **A value an option admits, the option admits as an option.** Every option is attempted, so
    `admitOptV` is the row itself and this is the identity. `Slice.lean` calls it by name. -/
theorem admitOptV_of_Adm {t : Term} {v : Value}
    (h : Adm t v = true) : admitOptV (specOf t, Adm t) v = true := h


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
  rw [Adm_meet _ _ _ h, show Adm (.union os) v = selOptV (AdmSpecs os) v from rfl,
    selOptV_eq_AdmAny]

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
  rw [AdmA_meet h, AdmA_union os a, selOptA_eq_AdmAAny]

/-- …and the distribution, written so a reader sees it: the meet of a term with a join is the
    join of the meets, one option at a time. -/
theorem AdmA_meet_union_distrib {x z o : Term} {os : List Term}
    (h : Term.meet x (.union (o :: os)) = some z) (a : Attr) :
    AdmA z a = ((AdmA x a && AdmA o a) || (AdmA x a && AdmAAny os a)) := by
  rw [AdmA_meet_union h, AdmAAny_cons]
  cases AdmA x a <;> cases AdmA o a <;> cases AdmAAny os a <;> rfl

/-! ## The typed fragment is closed under the meet

The meet builds unions, and a union of derivable options is derivable (`typed_ofOptions`), so
the rows that distribute a union owe only the survivors' derivability (`survivors`).

The object rows are the ones that would need a choice of index. They do not make one:
`typed_canon` restates a derivation at indices that are functions of the term, so the merged
field table is written down. -/

/-- Option judgements for a list, where each option has one. -/
theorem typedListμ_of_all : ∀ {ss : List Term}, (∀ t ∈ ss, ∃ T μ, Typed t T μ) →
    ∃ Ts μs, TypedListμ ss Ts μs
  | [], _ => ⟨[], [], .nil⟩
  | t :: ts, h => by
    obtain ⟨T, μ, hty⟩ := h t List.mem_cons_self
    obtain ⟨Ts, μs, hs⟩ := typedListμ_of_all (fun u hu => h u (List.mem_cons_of_mem _ hu))
    exact ⟨T :: Ts, μ :: μs, .cons hty hs⟩

/-- **A list of derivable survivors gives a derivable union.** -/
theorem typed_ofOptions {ss : List Term}
    (h : ∀ t ∈ ss, ∃ T μ, Typed t T μ) : ∃ T μ, Typed (Term.ofOptions ss) T μ := by
  rcases ss with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · exact ⟨_, _, Typed.never⟩
  · exact h a List.mem_cons_self
  · obtain ⟨Ts, μs, hL⟩ := typedListμ_of_all h
    exact ⟨_, _, Typed.union hL⟩


/-- Each option of a derivable union is derivable. -/
theorem typedListμ_mem : ∀ {os : List Term} {Ts μs}, TypedListμ os Ts μs →
    ∀ t ∈ os, ∃ T μ, Typed t T μ
  | _, _, _, .nil, _, ht => nomatch ht
  | _, _, _, .cons hty hs, t, ht => by
    rcases List.mem_cons.mp ht with rfl | ht'
    · exact ⟨_, _, hty⟩
    · exact typedListμ_mem hs t ht'

/-- …read off the judgement of the union itself. -/
theorem typed_union_inv {os : List Term} :
    (∃ T μ, Typed (.union os) T μ) → ∀ t ∈ os, ∃ T μ, Typed t T μ
  | ⟨_, _, h⟩ => by cases h with | union hL => exact typedListμ_mem hL

/-- …and the term under a refinement. -/
theorem typed_refine_inv {a : Term} {p : Pred} :
    (∃ T μ, Typed (.refine a p) T μ) → ∃ T μ, Typed a T μ
  | ⟨_, _, h⟩ => by cases h with | refine h' => exact ⟨_, _, h'⟩

/-- Normalising a refinement keeps it derivable: the bottom is derivable too. -/
theorem typed_refineOf {t : Term} {p : Pred} (h : ∃ T μ, Typed t T μ) :
    ∃ T μ, Typed (Term.refineOf t p) T μ := by
  obtain ⟨T, μ, hT⟩ := h
  cases t <;>
    first
      | exact ⟨_, _, Typed.refine hT⟩
      | exact ⟨_, _, Typed.never⟩
      | (simp only [Term.refineOf]
         split
         · obtain ⟨T', μ', hT'⟩ := typed_refine_inv ⟨_, _, hT⟩
           exact ⟨_, _, Typed.refine hT'⟩
         · exact ⟨_, _, Typed.never⟩
         · exact ⟨_, _, Typed.refine hT⟩)

/-- Judgements for a list, from one per element. -/
theorem typedList_of_all : ∀ {ts : List Term}, (∀ t ∈ ts, ∃ T μ, Typed t T μ) →
    ∃ Ts, TypedList ts Ts
  | [], _ => ⟨[], .nil⟩
  | t :: ts, h => by
    obtain ⟨T, μ, hty⟩ := h t List.mem_cons_self
    obtain ⟨Ts, hs⟩ := typedList_of_all (fun u hu => h u (List.mem_cons_of_mem _ hu))
    exact ⟨T :: Ts, .cons hty hs⟩

/-- …and for a tail. -/
theorem typedOpt_of_all : ∀ {tail : Option Term}, (∀ t ∈ tail, ∃ T μ, Typed t T μ) →
    ∃ Tt, TypedOpt tail Tt
  | none, _ => ⟨none, .none⟩
  | some t, h => by
    obtain ⟨T, μ, hty⟩ := h t rfl
    exact ⟨some T, .some hty⟩

/-- Normalising a tuple keeps it derivable: a declared position at the bottom gives the
    bottom, which is derivable. -/
theorem typed_listOf {pre : List Term} {sp : Option Term} {suf : List Term}
    (hp : ∀ t ∈ pre, ∃ T μ, Typed t T μ) (hs : ∀ t ∈ sp, ∃ T μ, Typed t T μ)
    (hf : ∀ t ∈ suf, ∃ T μ, Typed t T μ) :
    ∃ T μ, Typed (Term.listOf pre sp suf) T μ := by
  unfold Term.listOf
  split
  · exact ⟨_, _, Typed.never⟩
  · obtain ⟨Tp, hTp⟩ := typedList_of_all hp
    obtain ⟨Ts, hTs⟩ := typedOpt_of_all hs
    obtain ⟨Tf, hTf⟩ := typedList_of_all hf
    exact ⟨_, _, Typed.list hTp hTs hTf⟩

/-- …and the suffix-free case, under the name the tuple rows use. -/
theorem typed_tupleOf {ts : List Term} {tail : Option Term}
    (h : ∀ t ∈ ts, ∃ T μ, Typed t T μ) (ht : ∀ t ∈ tail, ∃ T μ, Typed t T μ) :
    ∃ T μ, Typed (Term.tupleOf ts tail) T μ :=
  typed_listOf h ht (by simp)

/-- Inversions for a tuple: each declared position, and the tail. -/
theorem typedList_mem : ∀ {ts : List Term} {Ts}, TypedList ts Ts → ∀ t ∈ ts, ∃ T μ, Typed t T μ
  | _, _, .nil, _, ht => nomatch ht
  | _, _, .cons hty hs, t, ht => by
    rcases List.mem_cons.mp ht with rfl | ht'
    · exact ⟨_, _, hty⟩
    · exact typedList_mem hs t ht'

/-- Inversions: a derivable container gives derivable components. -/
theorem typed_list_inv {pre : List Term} {sp : Option Term} {suf : List Term} :
    (∃ T μ, Typed (.list pre sp suf) T μ) →
    (∀ t ∈ pre, ∃ T μ, Typed t T μ) ∧ (∀ t ∈ sp, ∃ T μ, Typed t T μ) ∧
      (∀ t ∈ suf, ∃ T μ, Typed t T μ)
  | ⟨_, _, h⟩ => by
    cases h with
    | list hp hs hf =>
        refine ⟨typedList_mem hp, ?_, typedList_mem hf⟩
        cases hs with
        | none => exact fun t ht => nomatch ht
        | some hty => exact fun t ht => by cases ht; exact ⟨_, _, hty⟩

/-- …the element of a derivable array, which is the spread of the `list` it builds. -/
theorem typed_array_inv {a : Term} : (∃ T μ, Typed (.array a) T μ) → ∃ T μ, Typed a T μ :=
  fun h => (typed_list_inv h).2.1 a rfl

/-- …and both halves of a tuple at once, which is the form the four tuple rows take. -/
theorem typed_tuple_inv {ts : List Term} {tail : Option Term} :
    (∃ T μ, Typed (.tuple ts tail) T μ) →
    (∀ t ∈ ts, ∃ T μ, Typed t T μ) ∧ (∀ t ∈ tail, ∃ T μ, Typed t T μ) :=
  fun h => ⟨(typed_list_inv h).1, (typed_list_inv h).2.1⟩

/-- The term a slot carries. -/
def ObjectSlot.termOf : ObjectSlot → Term
  | .req t | .optional t => t

/-- **A derivation restated at indices that are functions of the term.** The held set of a
    derivable term is its denotation's and its member is `μSyn`'s, so an object row can write
    its field table down instead of choosing one. -/
theorem typed_canon {t : Term} (h : ∃ T μ, Typed t T μ) : Typed t (denote t).T (μSyn t) := by
  obtain ⟨T, μ, hT⟩ := h
  have h1 : (denote t).T = T := funext fun v => propext (typed_T_identity hT v)
  have h2 : μSyn t = μ := typed_μSyn hT
  rw [h1, h2]
  exact hT

/-- …and the same at a field, where the mark is `ObjectSlot.isReq`. -/
theorem typedField_canon {fd : ObjectSlot} (h : ∃ T μ, Typed (ObjectSlot.termOf fd) T μ) :
    TypedField fd (denote (ObjectSlot.termOf fd)).T (ObjectSlot.isReq fd) (μSyn (ObjectSlot.termOf fd)) := by
  cases fd with
  | req t => exact TypedField.req (typed_canon h)
  | optional t => exact TypedField.optional (typed_canon h)

/-- A typed field carries a derivable term, whichever mark it has. -/
theorem typedField_termOf {fd : ObjectSlot} {T π μ} (h : TypedField fd T π μ) :
    ∃ T' μ', Typed (ObjectSlot.termOf fd) T' μ' := by
  cases h with
  | req h' => exact ⟨_, _, h'⟩
  | optional h' => exact ⟨_, _, h'⟩

/-- Inversion for an object: every declared slot's term is derivable, and the open block is
    typed. -/
theorem typed_object_inv {b : Body} (h : ∃ T μ, Typed (.object b) T μ) :
    (∀ k, ∃ T μ, Typed (ObjectSlot.termOf (b.at k)) T μ) ∧ ∃ R, TypedWild b.wild R := by
  obtain ⟨T, μ, hT⟩ := h
  cases hT with
  | object hf hr => exact ⟨fun k => typedField_termOf (hf k), _, hr⟩

/-- A body with no open block has no open part in its held set. -/
theorem typedWild_none_of_closed {w : Option Term} {R : Option Held}
    (hw : w = none) (h : TypedWild w R) : R = none := by
  cases h <;> simp_all

section StructuralTyped
set_option maxHeartbeats 1000000

/-! ### The same three layers, on the structural meet

The shared inner owns every row that reads the right operand alone. The nine flat families own
one left constructor each, and each of their rows answers a factor or the bottom. The four
container families carry the recursion at a subterm. -/

/-- `f` carries derivability with one term fixed on the left, at EVERY right operand. -/
def TypedSound (x : Term) (f : Term → Option Term) : Prop :=
  ∀ y z, f y = some z → (∃ T μ, Typed x T μ) → (∃ T μ, Typed y T μ) → ∃ T μ, Typed z T μ

/-- `fam` carries derivability with one term fixed on the left, over the operands it is handed. -/
def TypedFam (x : Term) (fam : Term → Option Term) : Prop :=
  ∀ y z, Delegated y → fam y = some z → (∃ T μ, Typed x T μ) → (∃ T μ, Typed y T μ) →
    ∃ T μ, Typed z T μ

/-- An object is derivable where every declared slot's term is and the open block is typed: the
    indices are written down as functions of each slot's own term rather than chosen. -/
theorem typed_object_of {fs : Finset Name} {F : {k // k ∈ fs} → ObjectSlot}
    {w : Option Term}
    {R : Option Held} (hf : ∀ k, ∃ T μ, Typed (ObjectSlot.termOf (F k)) T μ)
    (hr : TypedWild w R) :
    ∃ T μ, Typed (.object (.mk fs F w)) T μ :=
  ⟨_, _, Typed.object (body := .mk fs F w) (R := R)
    (bind := fun k => (ObjectSlot.isReq (F k), (denote (ObjectSlot.termOf (F k))).T))
    (μs := fun k => μSyn (ObjectSlot.termOf (F k)))
    (fun k => typedField_canon (hf k)) hr⟩

mutual
/-- Every row that reads the right operand alone is derivable wherever the family is. -/
theorem typed_meetSRight {x : Term} {fam : Term → Option Term} (hf : TypedFam x fam)
    (hA : AdmFam x fam) :
    ∀ y z, meetSRight fam y = some z → (∃ T μ, Typed x T μ) → (∃ T μ, Typed y T μ) →
      ∃ T μ, Typed z T μ
  | .never, _, h, _, _ => by
      simp only [meetSRight, Option.some.injEq] at h; subst h; exact ⟨_, _, Typed.never⟩
  | .held _ _ _ _, _, h, _, _ => by simp [meetSRight] at h
  | .lazy t, _, h, hx, hy => by
      rw [meetSRight] at h
      refine typed_meetSRight hf hA t _ h hx ?_
      obtain ⟨T, μ, hT⟩ := hy
      cases hT with | lazy h' => exact ⟨_, _, h'⟩
  | .refine y p, _, h, hx, hy => by
      simp only [meetSRight] at h
      split at h
      · obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
        exact typed_refineOf (typed_meetSRight hf hA y w hw hx (typed_refine_inv hy))
      · exact absurd h (by simp)
  | .union os, _, h, hx, hy => by
      obtain ⟨zs, hF, rfl⟩ := meetSRight_union h
      exact typed_ofOptions (survivors hy
        ((typed_meetSRightL hf hA os zs hF).imp fun _ _ k => k hx)
        (List.filter_sublist (p := fun w : Term => !w.isNever)))
  | .string, _, h, hx, hy => hf .string _ trivial h hx hy
  | .number, _, h, hx, hy => hf .number _ trivial h hx hy
  | .boolean, _, h, hx, hy => hf .boolean _ trivial h hx hy
  | .binary, _, h, hx, hy => hf .binary _ trivial h hx hy
  | .null, _, h, hx, hy => hf .null _ trivial h hx hy
  | .literal k lv, _, h, hx, hy => hf (.literal k lv) _ trivial h hx hy
  | .set b, _, h, hx, hy => hf (.set b) _ trivial h hx hy
  | .opaq, _, h, hx, hy => hf .opaq _ trivial h hx hy
  | .list p q s, _, h, hx, hy => hf (.list p q s) _ trivial h hx hy
  | .object b, _, h, hx, hy => hf (.object b) _ trivial h hx hy
termination_by structural y => y

/-- The list companion: the union row's options, lifted pointwise. -/
theorem typed_meetSRightL {x : Term} {fam : Term → Option Term} (hf : TypedFam x fam)
    (hA : AdmFam x fam) :
    ∀ os zs, List.Forall₂ (fun t w => meetSRight fam t = some w) os zs →
      List.Forall₂ (fun t w => (∃ T μ, Typed x T μ) → (∃ T μ, Typed t T μ) →
        ∃ T μ, Typed w T μ) os zs
  | [], _, h => by cases h; exact .nil
  | t :: ts, _, h => by
      cases h with
      | cons hh ht =>
          exact .cons (fun hx hy => typed_meetSRight hf hA t _ hh hx hy)
            (typed_meetSRightL hf hA ts _ ht)
termination_by structural os => os
end

/-- The tactic every flat family uses: a row answers one of its factors, the bottom, or nothing. -/
local macro "typed_fam" fam:ident : tactic => `(tactic|
  (intro y z hd h hx hy
   cases y <;> first | exact hd.elim | skip
   all_goals
     (simp only [$fam:ident, Term.meetLit] at h
      repeat' split at h
      all_goals
        first
          | (simp only [reduceCtorEq] at h; done)
          | (simp only [Option.some.injEq] at h
             subst h
             first
               | exact hx
               | exact hy
               | exact ⟨_, _, Typed.never⟩
               | exact ⟨_, _, Typed.opaq⟩))))

/-- `string` meets its own literals and `opaque`, and each answer is a factor or the bottom. -/
theorem typed_famString : TypedFam Term.string famString := by typed_fam famString

/-- `number` likewise. -/
theorem typed_famNumber : TypedFam Term.number famNumber := by typed_fam famNumber

/-- `boolean` likewise. -/
theorem typed_famBoolean : TypedFam Term.boolean famBoolean := by typed_fam famBoolean

/-- `binary` likewise. -/
theorem typed_famBinary : TypedFam Term.binary famBinary := by typed_fam famBinary

/-- `null` likewise. -/
theorem typed_famNull : TypedFam Term.null famNull := by typed_fam famNull

/-- A literal meets its own base and an equal literal, and is the bottom elsewhere. -/
theorem typed_famLit (k : GroundKind) (lv : k.Carrier) :
    TypedFam (.literal k lv) (famLit k lv) := by typed_fam famLit

/-- Two set bases meet where they are equal. -/
theorem typed_famSet (b : SetBase) : TypedFam (.set b) (famSet b) := by typed_fam famSet

/-- `opaque` meets each self-identifying base, and another `opaque`. -/
theorem typed_famOpaq : TypedFam .opaq (famOpaq) := by typed_fam famOpaq

/-! ### The container families: the four that read the recursion. -/

/-- …and the same two tuples' positions zipped. -/
theorem typed_zipF_lift :
    ∀ {ts us : List Term} {fs : List (Term → Option Term)} {vs : List Term},
      List.Forall₂ TypedSound ts fs → (∀ t ∈ ts, ∃ T μ, Typed t T μ) →
      (∀ u ∈ us, ∃ T μ, Typed u T μ) →
      List.Forall₂ (fun (p : (Term → Option Term) × Term) v => p.1 p.2 = some v) (fs.zip us) vs →
      ∀ v ∈ vs, ∃ T μ, Typed v T μ := by
  intro ts
  induction ts with
  | nil => intro us fs vs hfs _ _ hv; cases hfs; cases hv; intro v hvm; exact nomatch hvm
  | cons t ts ihs =>
      intro us fs vs hfs hts hus hv
      cases hfs with
      | cons hf hfs' =>
          cases us with
          | nil => cases hv; intro v hvm; exact nomatch hvm
          | cons u us =>
              cases hv with
              | cons hh ht =>
                  intro v hvm
                  rcases List.mem_cons.mp hvm with rfl | hvm'
                  · exact hf u v hh (hts t List.mem_cons_self) (hus u List.mem_cons_self)
                  · exact ihs hfs' (fun w hw => hts w (List.mem_cons_of_mem _ hw))
                      (fun w hw => hus w (List.mem_cons_of_mem _ hw)) ht v hvm'

/-- **The one positional container's family, on the derivation.** Every term the answer holds
    is a meet of a term one shape declares with a term the other declares, and `rowOfG_mem`
    says a row holds nothing else. -/
theorem typed_famList {pre suf : List Term} {sp : Option Term}
    {fpre fsuf : List (Term → Option Term)} {fsp : Option (Term → Option Term)}
    (hp : List.Forall₂ TypedSound pre fpre)
    (hs : (sp = none ∧ fsp = none) ∨ ∃ t f, sp = some t ∧ fsp = some f ∧ TypedSound t f)
    (hf : List.Forall₂ TypedSound suf fsuf) :
    TypedFam (.list pre sp suf) (famList fpre fsp fsuf) := by
  intro y z hd h hx hy
  obtain ⟨hpre, hsp, hsuf⟩ := typed_list_inv hx
  cases y <;> first | exact hd.elim | skip
  case list pre₂ sp₂ suf₂ =>
      obtain ⟨hpre₂, hsp₂, hsuf₂⟩ := typed_list_inv hy
      have hall : ∀ t ∈ pre ++ suf, ∃ T μ, Typed t T μ := by
        intro w hw
        rcases List.mem_append.mp hw with h' | h'
        exacts [hpre w h', hsuf w h']
      simp only [famList] at h
      rcases hs with ⟨rfl, rfl⟩ | ⟨t, f, rfl, rfl, hsound⟩
      · simp only [listMeetRow] at h
        rw [show rowOfG fpre none fsuf (fpre.length + fsuf.length) = some (fpre ++ fsuf) from
          by rw [rowOfG_none_eq, if_pos rfl]] at h
        cases hR : rowOfG pre₂ sp₂ suf₂ (fpre.length + fsuf.length) with
        | none =>
            rw [hR] at h
            simp only [Option.some.injEq] at h
            subst h
            exact ⟨_, _, Typed.never⟩
        | some us =>
            rw [hR] at h
            obtain ⟨row, hrow, rfl⟩ := Option.map_eq_some_iff.mp h
            refine typed_listOf ?_ (by simp) (by simp)
            refine typed_zipF_lift (forall₂_append hp hf) hall ?_
              (allSome_map_forall₂ _ (by rw [← zipF_eq]; exact hrow))
            intro u hu
            rcases rowOfG_mem hR hu with h' | h' | h'
            exacts [hpre₂ u h', hsp₂ u h', hsuf₂ u h']
      · cases sp₂ with
        | none =>
            simp only [listMeetRow] at h
            rw [show rowOfG pre₂ none suf₂ (pre₂.length + suf₂.length)
                = some (pre₂ ++ suf₂) from by rw [rowOfG_none_eq, if_pos rfl]] at h
            cases hL : rowOfG fpre (some f) fsuf (pre₂.length + suf₂.length) with
            | none =>
                rw [hL] at h
                simp only [Option.some.injEq] at h
                subst h
                exact ⟨_, _, Typed.never⟩
            | some fs =>
                rw [hL] at h
                obtain ⟨row, hrow, rfl⟩ := Option.map_eq_some_iff.mp h
                obtain ⟨ts, hts, htsF⟩ :=
                  rowOfG_forall₂_left hp (Or.inr ⟨t, f, rfl, rfl, hsound⟩) hf hL
                refine typed_listOf ?_ (by simp) (by simp)
                refine typed_zipF_lift htsF ?_ ?_
                  (allSome_map_forall₂ _ (by rw [← zipF_eq]; exact hrow))
                · intro w hw
                  rcases rowOfG_mem hts hw with h' | h' | h'
                  exacts [hpre w h', hsp w h', hsuf w h']
                · intro u hu
                  rcases List.mem_append.mp hu with h' | h'
                  exacts [hpre₂ u h', hsuf₂ u h']
        | some c =>
            simp only [listMeetRow] at h
            split at h
            · next hdom =>
                obtain ⟨fs, hfs⟩ :=
                  rowOfG_total (pre := fpre) (suf := fsuf) (c := f)
                    (n := max fpre.length pre₂.length + max fsuf.length suf₂.length) (by omega)
                obtain ⟨us, hus⟩ :=
                  rowOfG_total (pre := pre₂) (suf := suf₂) (c := c)
                    (n := max fpre.length pre₂.length + max fsuf.length suf₂.length) (by omega)
                rw [hfs, hus] at h
                cases hfc : f c with
                | none => rw [hfc] at h; exact absurd h (by simp)
                | some spz =>
                    rw [hfc] at h
                    obtain ⟨row, hrow, rfl⟩ := Option.map_eq_some_iff.mp h
                    obtain ⟨ts, hts, htsF⟩ :=
                      rowOfG_forall₂_left hp (Or.inr ⟨t, f, rfl, rfl, hsound⟩) hf hfs
                    have hrowT : ∀ w ∈ row, ∃ T μ, Typed w T μ := by
                      refine typed_zipF_lift htsF ?_ ?_
                        (allSome_map_forall₂ _ (by rw [← zipF_eq]; exact hrow))
                      · intro w hw
                        rcases rowOfG_mem hts hw with h' | h' | h'
                        exacts [hpre w h', hsp w h', hsuf w h']
                      · intro u hu
                        rcases rowOfG_mem hus hu with h' | h' | h'
                        exacts [hpre₂ u h', hsp₂ u h', hsuf₂ u h']
                    refine typed_listOf (fun w hw => hrowT w (List.mem_of_mem_take hw)) ?_
                      (fun w hw => hrowT w (List.mem_of_mem_drop hw))
                    intro w hw
                    cases hw
                    exact hsound c spz hfc (hsp t rfl) (hsp₂ c rfl)
            · exact absurd h (by simp)
  case opaq => simp [famList] at h
  all_goals
    (simp only [famList, Option.some.injEq] at h; subst h; exact ⟨_, _, Typed.never⟩)

/-- A typed body's block is typed: the open block's term, or the bottom. -/
theorem typed_block {b : Body} (h : ∃ R, TypedWild b.wild R) : ∃ T μ, Typed b.block T μ := by
  obtain ⟨R, hR⟩ := h
  cases b with
  | mk fs f w =>
    cases hR with
    | none => exact ⟨_, _, Typed.never⟩
    | some ht => exact ⟨_, _, ht⟩

/-- **Two objects meet pointwise, and the meet stays in the typed fragment.** -/
theorem typed_famObj {a : Body} {g : {k // k ∈ a.fields} → ObjectSlot → Option ObjectSlot}
    {mw : Term → Option Term}
    (hg : ∀ (k : {k // k ∈ a.fields}) (fl fm : ObjectSlot), g k fl = some fm →
      (∃ T μ, Typed (ObjectSlot.termOf (a.at k)) T μ) → (∃ T μ, Typed (ObjectSlot.termOf fl) T μ) →
      ∃ T μ, Typed (ObjectSlot.termOf fm) T μ)
    (hw : ∀ y z, mw y = some z → (∃ T μ, Typed a.block T μ) → (∃ T μ, Typed y T μ) →
      ∃ T μ, Typed z T μ) :
    TypedFam (.object a) (famObj a g mw) := by
  intro y z hd h hx hy
  obtain ⟨hfa, hra⟩ := typed_object_inv hx
  cases y <;> first | exact hd.elim | skip
  case object b =>
      obtain ⟨hfb, hrb⟩ := typed_object_inv hy
      simp only [famObj] at h
      unfold objObj at h
      split at h
      next => simp only [Option.some.injEq] at h; subst h; exact ⟨_, _, Typed.never⟩
      next =>
        split at h
        next => exact absurd h (by simp)
        next zb hwz =>
          split at h
          next hall =>
            simp only [Option.some.injEq] at h; subst h
            have hF : ∀ k : {k // k ∈ (a.fields ∪ b.fields).filter (fun k =>
                (if h : k ∈ a.fields ∪ b.fields then
                  !(zb.isNever && ObjectSlot.isAbsentOpt (objSlot a b g mw ⟨k, h⟩))
                else false) = true)},
                ∃ T μ, Typed (ObjectSlot.termOf ((objSlot a b g mw
                  ⟨k.1, (Finset.mem_filter.mp k.2).1⟩).getD (.optional .never))) T μ := by
              intro k
              obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp
                (of_decide_eq_true hall ⟨k.1, (Finset.mem_filter.mp k.2).1⟩)
              rw [hs, Option.getD_some]
              unfold objSlot at hs
              split at hs
              next ha =>
                refine hg _ _ _ hs (hfa _) ?_
                split
                · exact hfb _
                · exact typed_block hrb
              next ha =>
                have hb := (Finset.mem_union.mp (Finset.mem_filter.mp k.2).1).resolve_left ha
                have hty := hfb ⟨k.1, hb⟩
                cases hf : b.at ⟨k.1, hb⟩ with
                | req y =>
                  rw [hf] at hs hty
                  simp only [ObjectSlot.through, Option.map_eq_some_iff] at hs
                  obtain ⟨z, hz, rfl⟩ := hs
                  exact hw _ _ hz (typed_block hra) hty
                | optional y =>
                  rw [hf] at hs hty
                  simp only [ObjectSlot.through, Option.map_eq_some_iff] at hs
                  obtain ⟨z, hz, rfl⟩ := hs
                  exact hw _ _ hz (typed_block hra) hty
            rcases Bool.eq_false_or_eq_true zb.isNever with hn | hn
            · rw [if_pos hn]
              exact typed_object_of hF TypedWild.none
            · obtain ⟨T, μ, ht⟩ := hw _ _ hwz (typed_block hra) (typed_block hrb)
              rw [if_neg (by rw [hn]; exact Bool.false_ne_true)]
              exact typed_object_of hF (TypedWild.some ht)
          next => exact absurd h (by simp)
  case opaq => simp [famObj] at h
  all_goals
    (simp only [famObj, Option.some.injEq] at h; subst h; exact ⟨_, _, Typed.never⟩)

/-! ### The outer theorem. -/

mutual
/-- **The typed fragment is closed under the meet.** Where two derivable terms have a meet, the
    meet is derivable. The union row owes only the survivors' derivability (`survivors`). -/
theorem typed_meet : ∀ x y z, Term.meet x y = some z →
    (∃ T μ, Typed x T μ) → (∃ T μ, Typed y T μ) → ∃ T μ, Typed z T μ
  | .never, _, _, h, _, _ => by
      simp only [Term.meet, Option.some.injEq] at h; subst h; exact ⟨_, _, Typed.never⟩
  | .held _ _ _ _, y, _, h, _, _ => by
      cases y <;>
        first
          | (simp only [Term.meet, Option.some.injEq] at h; subst h; exact ⟨_, _, Typed.never⟩)
          | exact absurd h (by simp [Term.meet])
  | .lazy x, y, _, h, hx, hy => by
      rw [Term.meet] at h
      refine typed_meet x y _ h ?_ hy
      obtain ⟨T, μ, hT⟩ := hx
      cases hT with | lazy h' => exact ⟨_, _, h'⟩
  | .refine x p, y, _, h, hx, hy => by
      cases y with
      | never =>
          simp only [Term.meet, Option.some.injEq] at h; subst h; exact ⟨_, _, Typed.never⟩
      | _ =>
        simp only [Term.meet] at h
        split at h
        · obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
          exact typed_refineOf (typed_meet x _ w hw (typed_refine_inv hx) hy)
        · exact absurd h (by simp)
  | .union os, y, _, h, hx, hy => by
      cases y with
      | never =>
          simp only [Term.meet, Option.some.injEq] at h; subst h; exact ⟨_, _, Typed.never⟩
      | _ =>
        obtain ⟨zs, hF, rfl⟩ := meet_union_of h (by simp)
        exact typed_ofOptions (survivors hx
          ((typed_meetL os _ zs hF).imp fun _ _ k ht => k ht hy)
          (List.filter_sublist (p := fun w : Term => !w.isNever)))
  | .string, y, z, h, hx, hy => typed_meetSRight typed_famString Adm_famString y z h hx hy
  | .number, y, z, h, hx, hy => typed_meetSRight typed_famNumber Adm_famNumber y z h hx hy
  | .boolean, y, z, h, hx, hy => typed_meetSRight typed_famBoolean Adm_famBoolean y z h hx hy
  | .binary, y, z, h, hx, hy => typed_meetSRight typed_famBinary Adm_famBinary y z h hx hy
  | .null, y, z, h, hx, hy => typed_meetSRight typed_famNull Adm_famNull y z h hx hy
  | .literal k lv, y, z, h, hx, hy => typed_meetSRight (typed_famLit k lv) (Adm_famLit k lv) y z h hx hy
  | .set b, y, z, h, hx, hy => typed_meetSRight (typed_famSet b) (Adm_famSet b) y z h hx hy
  | .opaq, y, z, h, hx, hy => typed_meetSRight (typed_famOpaq) (Adm_famOpaq) y z h hx hy
  | .list pre sp suf, y, z, h, hx, hy => by
      cases sp with
      | none =>
          exact typed_meetSRight (typed_famList (pre := pre) (sp := none) (suf := suf)
            (typed_meetSTs pre) (Or.inl ⟨rfl, rfl⟩) (typed_meetSTs suf))
            (Adm_famList (pre := pre) (sp := none) (suf := suf)
              (Adm_meetSTs pre) (Or.inl ⟨rfl, rfl⟩) (Adm_meetSTs suf)) y z h hx hy
      | some t =>
          exact typed_meetSRight (typed_famList (pre := pre) (sp := some t) (suf := suf)
            (typed_meetSTs pre)
            (Or.inr ⟨t, Term.meet t, rfl, rfl, fun u w hw => typed_meet t u w hw⟩)
            (typed_meetSTs suf))
            (Adm_famList (pre := pre) (sp := some t) (suf := suf)
              (Adm_meetSTs pre)
              (Or.inr ⟨t, Term.meet t, rfl, rfl, fun u w hw => Adm_meet t u w hw⟩)
              (Adm_meetSTs suf)) y z h hx hy
  | .object (.mk fs f none), y, z, h, hx, hy =>
      typed_meetSRight (typed_famObj (a := .mk fs f none)
        (fun k fl fm hm => typed_Field_meet (f k) fl fm hm)
        (fun _ _ hz _ _ => by
          simp only [Option.some.injEq] at hz; subst hz; exact ⟨_, _, Typed.never⟩))
        (Adm_famObj (a := .mk fs f none)
          (fun k fl fm hm w => Adm_Field_meet (f k) fl fm hm w)
          (fun _ _ _ hm => isReq_Field_meet hm)
          (fun _ _ hz _ => by simp only [Option.some.injEq] at hz; subst hz; rfl)) y z h hx hy
  | .object (.mk fs f (some t)), y, z, h, hx, hy =>
      typed_meetSRight (typed_famObj (a := .mk fs f (some t))
        (fun k fl fm hm => typed_Field_meet (f k) fl fm hm)
        (fun u w hw => typed_meet t u w hw))
        (Adm_famObj (a := .mk fs f (some t))
          (fun k fl fm hm w => Adm_Field_meet (f k) fl fm hm w)
          (fun _ _ _ hm => isReq_Field_meet hm)
          (fun u w hw => Adm_meet t u w hw)) y z h hx hy
termination_by structural x => x

/-- The union row's options, lifted pointwise at the fixed partner. -/
theorem typed_meetL : ∀ (os : List Term) (y : Term) (zs : List Term),
    List.Forall₂ (fun t w => Term.meet t y = some w) os zs →
    List.Forall₂ (fun t w => (∃ T μ, Typed t T μ) → (∃ T μ, Typed y T μ) →
      ∃ T μ, Typed w T μ) os zs
  | [], _, _, h => by cases h; exact .nil
  | t :: ts, y, _, h => by
      cases h with
      | cons hh ht =>
          exact .cons (fun hx hy => typed_meet t y _ hh hx hy) (typed_meetL ts y _ ht)
termination_by structural os => os

/-- Every position of a tuple carries the meet at that position. -/
theorem typed_meetSTs : ∀ ts : List Term, List.Forall₂ TypedSound ts (Term.meetSTs ts)
  | [] => .nil
  | t :: ts => .cons (fun u w hw => typed_meet t u w hw) (typed_meetSTs ts)
termination_by structural ts => ts

/-- Two fields at one name carry two terms that meet. -/
theorem typed_Field_meet : ∀ (f fl : ObjectSlot) (fm : ObjectSlot), ObjectSlot.meet f fl = some fm →
    (∃ T μ, Typed (ObjectSlot.termOf f) T μ) → (∃ T μ, Typed (ObjectSlot.termOf fl) T μ) →
    ∃ T μ, Typed (ObjectSlot.termOf fm) T μ
  | .req x, .req y, _, h, hx, hy => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact typed_meet x y tz hz hx hy
  | .req x, .optional y, _, h, hx, hy => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact typed_meet x y tz hz hx hy
  | .optional x, .req y, _, h, hx, hy => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact typed_meet x y tz hz hx hy
  | .optional x, .optional y, _, h, hx, hy => by
      obtain ⟨tz, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact typed_meet x y tz hz hx hy
termination_by structural f => f
end

end StructuralTyped



end Calculus
