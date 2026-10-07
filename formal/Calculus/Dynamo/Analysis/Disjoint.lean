import Calculus.Lang.DisjointA
import Calculus.Lang.View
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
are apart where no value is both (`Ground.apart`), and two data predicates are apart where no
value satisfies both (`Pred.apart`). DynamoDB supplies the laws of the leaves and of the set
former (`dynLeafAdm`, `dynFormerAdm` and their read-side twins), and the shape classes
(`dynShapes`).

**The certificate reads the views, not the terms.** A term denotes a partial isomorphism.
The caller view states its domain, and the stored view states its range. A `held` carries an adapter word,
and the test reads no table, so the test reads a raw `held` as disjoint from the bottom alone. The views replace each `held`
by a term that bounds its domain or its range, so the certificate asks the test of the two pairs
of views (`viewsDisjoint`). Two terms whose domains are disjoint and whose ranges are disjoint are
orthogonal: no value has two writers, and no attribute has two readers.

**The two halves part at a `held`.** A `held` writes where its caller-side term writes and reads
where its inner term reads, so an adapter and a native of the adapter's stored kind are disjoint
on the write half and not on the read half. The certificate asks both halves.
-/

namespace Calculus

open Alg (Orient Term.isNever ObjectSlot.isReqAt Body.fields_mk Body.wild_mk Body.at_mk Body.block view)

export Alg (Term.ofOptions hasHeld pair0)


/-! ## Reading a field and a term -/

/-- Whether a predicate is data that the test can compare with another. `closure` is the
    caller's own function and is the one case `Pred` keeps open. -/
def Pred.isData : Pred → Bool
  | .closure _ => false
  | _ => true

/-- One base's guard names one inhabitant. -/
theorem inL_inj {k : GroundKind} {x y : k.Carrier} {v : Value}
    (hx : inL k x v = true) (hy : inL k y v = true) : x = y :=
  Option.some_injective _ <| (k.prism.out_eq_some.mpr (inL_iff.mp hx)).symm.trans
    (k.prism.out_eq_some.mpr (inL_iff.mp hy))

/-- **Two predicates apart**: no value satisfies both. Two alternative sets over one base are apart
    where they share no alternative; an alternative set and an exclusion over one base are apart
    where every alternative is excluded; two predicates over two different bases are apart, except
    two exclusions, which share every value of a third base. A `closure` is apart from nothing,
    because nothing reads a caller's function. -/
def Pred.apart : Pred → Pred → Bool
  | .members k A, .members k' B =>
      if h : k' = k then (A.1.filter (fun x => x ∈ (h ▸ B).1)).card == 0 else true
  | .members k A, .except k' B =>
      if h : k' = k then (A.1.filter (fun x => x ∉ (h ▸ B).1)).card == 0 else true
  | .except k B, .members k' A =>
      if h : k = k' then (A.1.filter (fun x => x ∉ (h ▸ B).1)).card == 0 else true
  | .except k _, .except k' _ => !decide (k' = k)
  | _, _ => false

/-- **An alternative shared by two sets is the only way both hold.** `inL` names one inhabitant
    per base, so a value that satisfies an alternative of each set satisfies one alternative
    lying in both. -/
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

/-- **Two alternative sets over one base that share no alternative share no value.** -/
theorem memMem_empty {k : GroundKind} [DecidableEq k.Carrier] {A B : NEFinset k.Carrier}
    (hne : (A.1.filter (fun x => x ∈ B.1)).card = 0) (v : Value) :
    (inLs k A v && inLs k B v) = false := by
  have hne : A.1.filter (fun x => x ∈ B.1) = ∅ := Finset.card_eq_zero.mp hne
  have hiff := exists_filter_iff A.1 B.1 v
  rw [hne] at hiff
  simp only [Finset.notMem_empty, false_and, exists_false, false_iff, not_and] at hiff
  cases hA : inLs k A v with
  | false => simp
  | true =>
      cases hB : inLs k B v with
      | false => simp
      | true =>
          exact absurd (inLs_eq_true.mp hB) (hiff (inLs_eq_true.mp hA))

/-- An alternative that `inL` holds at a value names the value's base. -/
theorem inBase_of_inL {k : GroundKind} {x : k.Carrier} {v : Value} (h : inL k x v = true) :
    inBase k v = true := by
  rw [inL_iff.mp h]; exact decide_eq_true (k.summand.hμ x)

/-- A value outside a base satisfies no alternative at that base. -/
theorem inLs_false_of_base {k : GroundKind} {A : NEFinset k.Carrier} {v : Value}
    (h : inBase k v = false) : inLs k A v = false := by
  cases hA : inLs k A v with
  | false => rfl
  | true =>
    obtain ⟨x, _, hx⟩ := inLs_eq_true.mp hA
    rw [inBase_of_inL hx] at h
    exact nomatch h

/-- Two different bases hold no common value. -/
theorem inBase_disj {k k' : GroundKind} (h : k ≠ k') (v : Value) :
    (inBase k v && inBase k' v) = false :=
  Bool.eq_false_iff.mpr fun hv => h <| GroundKind.member_inj <|
    (of_decide_eq_true (Bool.and_eq_true _ _ ▸ hv).1).symm.trans
      (of_decide_eq_true (Bool.and_eq_true _ _ ▸ hv).2)

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
    (B : NEFinset k'.Carrier) (v : Value) :
    (Pred.eval (.members k A) v && Pred.eval (.members k' B) v) = false := by
  rw [Pred.eval_members, Pred.eval_members]
  have hd := inBase_disj h v
  cases hk : inBase k v with
  | false => rw [inLs_false_of_base hk]; rfl
  | true =>
    rw [hk, Bool.true_and] at hd
    rw [inLs_false_of_base hd, Bool.and_false]

/-- `members` and `except` at two different bases share no value. -/
theorem memExc_none {k k' : GroundKind} (h : k ≠ k') (A : NEFinset k.Carrier)
    (B : NEFinset k'.Carrier) (v : Value) :
    (Pred.eval (.members k A) v && Pred.eval (.except k' B) v) = false := by
  rw [Pred.eval_members, Pred.eval_except]
  have hd := inBase_disj h v
  cases hk : inBase k v with
  | false => rw [inLs_false_of_base hk]; rfl
  | true =>
    rw [hk, Bool.true_and] at hd
    rw [hd, Bool.false_and, Bool.and_false]

/-- `except` at two different bases share no value. -/
theorem excExc_none {k k' : GroundKind} (h : k ≠ k') (A : NEFinset k.Carrier)
    (B : NEFinset k'.Carrier) (v : Value) :
    (Pred.eval (.except k A) v && Pred.eval (.except k' B) v) = false := by
  rw [Pred.eval_except, Pred.eval_except]
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

/-- **An alternative set whose every alternative is excluded shares no value with the
    exclusion.** -/
theorem memExc_empty {k : GroundKind} [DecidableEq k.Carrier] {A B : NEFinset k.Carrier}
    (hne : (A.1.filter (fun x => x ∉ B.1)).card = 0) (v : Value) :
    (inLs k A v && (inBase k v && !inLs k B v)) = false := by
  have hne : A.1.filter (fun x => x ∉ B.1) = ∅ := Finset.card_eq_zero.mp hne
  have hiff := exists_filter_not_iff A.1 B.1 v
  cases hA : inLs k A v with
  | false => rfl
  | true =>
    cases hB : inLs k B v with
    | true => simp
    | false =>
      obtain ⟨x, hx, _⟩ :=
        hiff.mpr ⟨inLs_eq_true.mp hA, fun h => nomatch hB.symm.trans (inLs_eq_true.mpr h)⟩
      rw [hne] at hx
      exact absurd hx (Finset.notMem_empty x)

/-- **Two predicates apart hold together nowhere.** -/
theorem Pred.apart_sound : ∀ q p : Pred, Pred.apart q p = true →
    ∀ v, (Pred.eval q v && Pred.eval p v) = false
  | .members k A, .members k' B, h, v => by
      simp only [Pred.apart] at h
      split at h
      · next hk => subst hk; exact memMem_empty (beq_iff_eq.mp h) v
      · next hk => exact memMem_none (Ne.symm hk) A B v
  | .members k A, .except k' B, h, v => by
      simp only [Pred.apart] at h
      split at h
      · next hk => subst hk; exact memExc_empty (beq_iff_eq.mp h) v
      · next hk => exact memExc_none (Ne.symm hk) A B v
  | .except k B, .members k' A, h, v => by
      simp only [Pred.apart] at h
      rw [Bool.and_comm]
      split at h
      · next hk => subst hk; exact memExc_empty (beq_iff_eq.mp h) v
      · next hk => exact memExc_none (Ne.symm hk) A B v
  | .except k A, .except k' B, h, v => by
      simp only [Pred.apart, Bool.not_eq_true', decide_eq_false_iff_not] at h
      exact excExc_none (Ne.symm h) A B v
  | .members _ _, .closure _, h, _ | .except _ _, .closure _, h, _ | .closure _, _, h, _ => by
      simp [Pred.apart] at h


/-! ## The leaves of DynamoDB

The test is `Alg.Term.disjoint`, the structural test over a universe signature. DynamoDB supplies
the leaves `dynLeaf`: two primitives, and two predicates. -/

/-- **Two primitives apart.** A base shares its values with its own base and its own literals, and
    two literals share a value where they are one value. Every other pair is apart. -/
def Ground.apart : Ground → Ground → Bool
  | .base k, .base k' => !decide (k' = k)
  | .base k, .literal k' _ => !decide (k' = k)
  | .literal k _, .base k' => !decide (k' = k)
  | .literal k v, .literal k' v' => if h : k' = k then !decide (v = h ▸ v') else true

/-- **The leaves of DynamoDB.** -/
instance dynLeaf : Alg.Leaf dynSig where
  primsApart := Ground.apart
  isData s := Alg.half (X := fun s => dynP s → Bool) s Pred.isData fun _ => false
  predicatesApart s := Alg.half (X := fun s => dynP s → dynP s → Bool) s Pred.apart
    fun _ _ => false

/-! ## The union certificate

The certificate is defined here, after the leaves, because the test of the views reads them. -/

/-- **Whether the two pairs of views are disjoint**: the certificate for one pair of options. A
    term denotes a partial isomorphism. The caller view states its domain and the stored view
    states its range. Where the domains are disjoint and the ranges are disjoint, the product of
    the two domain idempotents is zero and the product of the two range idempotents is zero: the
    two options are orthogonal elements of an inverse semigroup (Lawson, *Primer on inverse
    semigroups I*, Lemma 2.16). So no value has two writers and no attribute has two readers
    (`viewsDisjoint_adm`, `viewsDisjoint_admA`).

    **The views state the domain and the range of a `held`**, which the test does not read on a
    raw term. On a term with no `held`, the caller view is the term, and the stored view keeps
    each predicate over a closed held-free inner term.

    **A `refine` at a `closure` has an admission that is a function.** The test reads it through
    its inner term. So `refine string (closure q)` beside `list [] (some number) []` is
    certified, because `string` beside the list is disjoint. -/
def viewsDisjoint (x y : Term) : Bool :=
  Alg.Term.disjoint pair0 (view .host x) (view .host y) &&
    Alg.Term.disjoint pair0 (view .dual x) (view .dual y)

/-- **The certificate a union must carry for its admission to be the join of its options'**: the
    certificate over a list of options, pair by pair. One condition. Each pair of options is
    certified, so no value and no attribute has two admitters, and nothing is refused for being
    admitted twice.

    An open object needs no second condition. The structural lemmas carry the open block
    themselves, so a union holding an open block certifies on separation alone. -/
def certAll : List Term → Bool
  | [] => true
  | t :: ts => ts.all (fun u => viewsDisjoint t u) && certAll ts

/-- The certificate, in the pairwise form. -/
theorem pairwise_of_certAll : ∀ {ts : List Term}, certAll ts = true →
    List.Pairwise (fun x y => viewsDisjoint x y = true) ts
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
  simp [Adm_rows, valPresentT, ObjectSlot.isReqAt, objAdmV, entryP, MapOf.at]
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
example : certAll [.object (.mk {"a"} (fun _ => .req .string) none),
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

/-- **A refinement is apart from a refined union in both orders.** The right union refines
    `literal "a" ∪ number` to `literal "b"`, and the test reads the predicate of the right
    refinement on each option below it. -/
theorem disjoint_refinedUnion_bothOrders :
    Alg.Term.disjoint pair0 (.refine Term.string (.members .string (NEFinset.of "b" ∅)) () : Term)
        (.union [.refine (.union [.refine Term.string (.members .string (NEFinset.of "a" ∅)) (),
          Term.number]) (.members .string (NEFinset.of "b" ∅)) (), Term.number]) = true ∧
      Alg.Term.disjoint pair0
        (.union [.refine (.union [.refine Term.string (.members .string (NEFinset.of "a" ∅)) (),
          Term.number]) (.members .string (NEFinset.of "b" ∅)) (), Term.number] : Term)
        (.refine Term.string (.members .string (NEFinset.of "b" ∅)) ()) = true := by
  decide

/-- **Two recursive terms are apart in both orders where a refinement covers one.** A list of
    booleans and a refined list of strings share no value, and the test reads the recursive
    term below the refinement on the right as it reads the term on the left. -/
theorem disjoint_refinedRecursion_bothOrders :
    Alg.Term.disjoint pair0
        (.mu (.union [Term.boolean, .object (.mk {"k"} (fun _ => .req (.var 0)) none)]) : Term)
        (.refine (.mu (.union [Term.string, .object (.mk {"k"} (fun _ => .req (.var 0)) none)]))
          (.closure fun _ => true) ()) = true ∧
      Alg.Term.disjoint pair0
        (.refine (.mu (.union [Term.string, .object (.mk {"k"} (fun _ => .req (.var 0)) none)]))
          (.closure fun _ => true) () : Term)
        (.mu (.union [Term.boolean, .object (.mk {"k"} (fun _ => .req (.var 0)) none)])) = true := by
  decide

/-- **The certificate of a union does not read the order of the options.** A recursive term
    beside a `held` over a refined recursive term is certified in both orders. -/
theorem viewsDisjoint_heldRecursion_bothOrders :
    viewsDisjoint (.mu (.union [Term.boolean, .object (.mk {"k"} (fun _ => .req (.var 0)) none)]))
        (.held false Term.string (.refine (.mu (.union [Term.string,
          .object (.mk {"k"} (fun _ => .req (.var 0)) none)])) (.closure fun _ => true) ())
          (.caller 0, false) []) = true ∧
      viewsDisjoint (.held false Term.string (.refine (.mu (.union [Term.string,
          .object (.mk {"k"} (fun _ => .req (.var 0)) none)])) (.closure fun _ => true) ())
          (.caller 0, false) [])
        (.mu (.union [Term.boolean, .object (.mk {"k"} (fun _ => .req (.var 0)) none)])) = true := by
  decide

example : certAll [.object (.mk {"x"} (fun _ => .optional .string) none)] = true := by
  simp [certAll]

example : certAll [.object (.mk {"x"} (fun _ => .req .string) none)]
    = true := by
  simp [certAll]

/-- …and a singleton union of an **open** object is certified: a union of one option has no
    pair to certify. -/
example : certAll [.object (.mk {"a"} (fun _ => .req .string) (some .string))]
    = true := by
  simp [certAll]

/-! ### Arrays told apart by a literal position

The owner's witness. Each list below starts with a literal, and the empty list is an option of
its own. Each pair is disjoint. -/

/-- The three options: a nonempty list of `"A"`, a nonempty list of `"B"`, and the empty list. -/
def literalListOptions : List Term :=
  [.list [.literal .string "A"] (some (.literal .string "A")) [],
   .list [.literal .string "B"] (some (.literal .string "B")) [],
   .list [] none []]

/-- **The test certifies the union**: each pair is disjoint. -/
theorem certAll_literalListOptions : certAll literalListOptions = true := by decide

/-- **The crossing control is not certified.** `array (literal "A")` and `array (literal "B")`
    both hold `[]`. -/
theorem not_certAll_literalArrays :
    certAll [.array (.literal .string "A"), .array (.literal .string "B")] = false := by decide

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
theorem viewsDisjoint_heldNE :
    viewsDisjoint (.held false (.set .string) (.list [.string] (some .string) []) (.caller 0, false) [])
      (.list [] (some .number) []) = true := by
  decide

/-- **A caller side that admits the empty list is refused**, because the list of numbers admits
    the empty list too. -/
theorem viewsDisjoint_heldAny :
    viewsDisjoint (.held false (.set .string) (.list [] (some .string) []) (.caller 0, false) [])
      (.list [] (some .number) []) = false := by
  decide

/-- **A `held` below a recursion is certified where the views part.** The caller view of the
    recursive term is `mu (union [literal "1", list [] (some (var 0)) []])`, and the stored view
    is `mu (union [number, list [] (some (var 0)) []])`. Each is disjoint from
    `literal "A" ∪ literal "B"`. -/
theorem viewsDisjoint_heldBelowMu :
    viewsDisjoint (.union [.literal .string "A", .literal .string "B"])
      (.mu (.union [.held false .number (.literal .string "1") (.caller 0, false) [], .list [] (some (.var 0)) []]))
      = true := by
  decide

/-- …and the pair is refused where the caller views share a value: the text `"1"`. -/
theorem viewsDisjoint_heldBelowMu_meets :
    viewsDisjoint (.literal .string "1")
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

/-- **Two sets whose element codecs move no common datum move no common set**, at an orientation,
    because no set is empty. -/
theorem setCodec_apart {o : Orient} {c d : Codec}
    (h : ∀ w, (c.f o w).isSome = true → (d.f o w).isSome = true → False) (x : Attr)
    (hc : ((setCodec c).f o x).isSome = true) (hd : ((setCodec d).f o x).isSome = true) : False := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hc
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hd
  obtain ⟨k, S, rfl, hS⟩ := setCodec_f_eq.mp hp
  obtain ⟨y, hy⟩ := S.2
  exact h _ (setAt_elem hS y hy) (setAt_elem (setCodec_wire_f.symm.trans hq) y hy)

/-- **Two sets whose elements share no value share no set.** -/
theorem Adm_set_and_false {a y : Term} (h : ∀ u, (Adm α a u && Adm α y u) = false) (v : Value) :
    (Adm α (.set a) v && Adm α (.set y) v) = false :=
  Bool.eq_false_iff.mpr fun hv => by
    rw [Bool.and_eq_true] at hv
    refine setCodec_apart (o := .host) (fun w h1 h2 => ?_) v
      ((Adm_exact (.set a) v).mp hv.1) ((Adm_exact (.set y) v).mp hv.2)
    have := h w
    rw [(Adm_exact a w).mpr h1, (Adm_exact y w).mpr h2] at this
    exact Bool.noConfusion this

/-- **Two primitives apart share no value.** -/
theorem Adm_prim_apart : ∀ g g' : Ground, Ground.apart g g' = true →
    ∀ v, (Adm α (.prim g) v && Adm α (.prim g') v) = false
  | .base k, .base k', hp, v => by
      simp only [Ground.apart, Bool.not_eq_true', decide_eq_false_iff_not] at hp
      exact inBase_disj (Ne.symm hp) v
  | .base k, .literal k' x, hp, v => by
      simp only [Ground.apart, Bool.not_eq_true', decide_eq_false_iff_not] at hp
      rw [Bool.and_comm]; exact (inL_and_inBase x v).trans (if_neg hp)
  | .literal k x, .base k', hp, v => by
      simp only [Ground.apart, Bool.not_eq_true', decide_eq_false_iff_not] at hp
      exact (inL_and_inBase x v).trans (if_neg (Ne.symm hp))
  | .literal k x, .literal k' x', hp, v => by
      refine Bool.eq_false_iff.mpr fun hv => ?_
      rw [Bool.and_eq_true] at hv
      have e := (inL_iff.mp (hv.1 : inL k x v = true)).symm.trans
        (inL_iff.mp (hv.2 : inL k' x' v = true))
      obtain rfl := GroundKind.member_inj ((k.summand.hμ x).symm.trans (e ▸ k'.summand.hμ x'))
      obtain rfl := Option.some_injective _
        ((k.prism.out_into x).symm.trans (e ▸ k.prism.out_into x'))
      simp [Ground.apart] at hp

/-- The former class of a kind: the five scalar kinds are one class. -/
def Kind.former : Kind → Alg.Former
  | .string | .number | .boolean | .binary | .null => .prim
  | .set => .set
  | .array => .list
  | .map => .object

/-- The former class of an attribute: the class of its kind. -/
abbrev Attr.former (a : Attr) : Alg.Former := a.kind.former

/-- A primitive writes only scalar data. -/
theorem ground_former (g : Ground) (v : Value) (h : ((groundCodec g).e v).isSome = true) :
    Attr.former v = .prim := by
  have h' := (Alg.PrimAdm.admV_exact (S := dynSyn) g v).mpr h
  obtain ⟨k, hk⟩ : ∃ k : GroundKind, v.member = k.member := by
    cases g with
    | base k => exact ⟨k, of_decide_eq_true (h' : inBase k v = true)⟩
    | literal k x => exact ⟨k, inL_iff.mp (h' : inL k x v = true) ▸ k.summand.hμ x⟩
  exact (congrArg (fun m : Member => m.kind.former) hk).trans (by cases k <;> rfl)

/-- **The shape classes of DynamoDB.** A base or a literal writes and reads a scalar, `setCodec`
    writes and reads one of the three sets, and the prisms build `arr`, `l`, `map` and `m`. -/
instance dynShapes : Alg.Shapes dynSyn where
  former := Attr.former
  prim := Alg.Orient.both
    (P := fun o => ∀ g v, ((Alg.Syn.ground (S := dynSyn) g).f o v).isSome = true → Attr.former v = .prim)
    ground_former fun g a h => ground_former g a (by rw [ground_selfdual]; exact h)
  set L hL c o v h := by
    cases hL
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨k, S, rfl, -⟩ := setCodec_f_eq.mp ha
    cases k <;> rfl
  list L hL _ := by cases hL; rfl
  map F hF _ := by cases hF; rfl

/-- The set former of DynamoDB: the set law of `setCodec`. -/
instance dynFormerAdm : Alg.FormerAdm dynSyn where
  set_never {_ β} _ _ h v := by
    obtain rfl : β = dynTableA := funext fun g => nomatch g
    exact Adm_set_and_false h v

/-- The leaves of DynamoDB keep apart the primitives that they say are apart, on the write side. -/
instance dynLeafAdm : Alg.LeafAdm dynSyn where
  prims_apart {_ β} g g' hp v := by
    obtain rfl : β = dynTableA := funext fun g => nomatch g
    exact Adm_prim_apart g g' hp v

/-- The predicate leaves of DynamoDB hold together nowhere where they are apart. The store names
    no predicate but the truth, so no two stored predicates are apart. -/
instance dynLeafMeet : Alg.LeafMeet dynSig where
  predicates_apart
    | false, q, p, h, v => Pred.apart_sound q p h v
    | true, _, _, h, _ => nomatch h

/-! ## DynamoDB is an instance of the laws, on the read side

`Alg.disjoint_soundA` proves the read side once, over any signature. DynamoDB supplies the read
law of its set former (`dynFormerAdmA`) and of its primitives (`dynLeafAdmA`). Each primitive is
self-dual, so the read law of the primitives is their write law. -/

/-- **Two sets whose elements read no common attribute read no common set.** -/
theorem AdmA_set_and_false {a y : Term} (h : ∀ u, (AdmA α a u && AdmA α y u) = false) (att : Attr) :
    (AdmA α (.set a) att && AdmA α (.set y) att) = false :=
  Bool.eq_false_iff.mpr fun hv => by
    rw [Bool.and_eq_true] at hv
    refine setCodec_apart (o := .dual) (fun w h1 h2 => ?_) att
      ((AdmA_exact (.set a) att).mp hv.1) ((AdmA_exact (.set y) att).mp hv.2)
    have := h w
    rw [(AdmA_exact a w).mpr h1, (AdmA_exact y w).mpr h2] at this
    exact Bool.noConfusion this

/-- **Two primitives apart read nothing together.** Each primitive is self-dual, so its read-side
    row is its write-side row (`PrimAdm.dual`). -/
theorem admA_prim_apart : ∀ g g' : Ground, Ground.apart g g' = true →
    ∀ a, (AdmA α (.prim g) a && AdmA α (.prim g') a) = false :=
  Adm_prim_apart (α := α)

/-- The set former of DynamoDB, on the read side. -/
instance dynFormerAdmA : Alg.FormerAdmA dynSyn where
  set_never {β _} _ _ h c := by
    obtain rfl : β = dynTableA := funext fun g => nomatch g
    exact AdmA_set_and_false h c

/-- The primitives of DynamoDB keep apart the primitives that they say are apart, on the read
    side. -/
instance dynLeafAdmA : Alg.LeafAdmA dynSyn where
  prims_apart {β _} g g' hp c := by
    obtain rfl : β = dynTableA := funext fun g => nomatch g
    exact admA_prim_apart g g' hp c


/-! ## The orthogonal row -/

/-- **Orthogonal terms admit no common value.** A value that both terms admit is admitted by
    both caller views, and the views are disjoint. -/
theorem viewsDisjoint_adm {x y : Term} (h : viewsDisjoint x y = true) (v : Value) :
    (Adm α x v && Adm α y v) = false := by
  simp only [viewsDisjoint, Bool.and_eq_true] at h
  exact Alg.views_apart (S := dynSyn) α dynTableA h.1 [] [] v

/-- **Orthogonal terms read no common attribute.** An attribute that both terms read is read
    by both stored views, and the views are disjoint. -/
theorem viewsDisjoint_admA {x y : Term} (h : viewsDisjoint x y = true) (a : Attr) :
    (AdmA α x a && AdmA α y a) = false := by
  simp only [viewsDisjoint, Bool.and_eq_true] at h
  have : Alg.Shapes ⟨dynSig, Orient.dual⟩ := Alg.Shapes.op (S := dynSyn)
  exact Alg.views_apart (S := dynSyn.op) dynTableA α h.2 [] [] a

/-- **The pair certificate is sound**: orthogonality separates the pair. -/
theorem separates_of_viewsDisjoint {x y : Term} (h : viewsDisjoint x y = true) : Separates α x y := by
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
    viewsDisjoint (.set (.refine (.held false .string (.union [.string, .boolean]) (.caller 0, false) [])
        (.closure fun _ => true) ()))
      (.set (.held false .number (.union [.number, .boolean]) (.caller 1, false) [])) = false := by
  decide

/-- **The certificate refuses a separated pair at a data predicate over a variable.** The pair is
    separated: `mu (refine (union [string, array (var 0)]) {a})` admits the string `"a"` and no
    other string, and `refine string {b}` admits the string `"b"` alone. The test compares two
    data predicates only over closed held-free inner terms, and this inner term holds a variable.
    So `viewsDisjoint` answers `false`. The host builds no data predicate over a variable, so no
    observable distinguishes this test from a finer test. A finer test becomes necessary only
    when the host builds such a term. -/
example :
    viewsDisjoint (.mu (.refine (.union [.string, .array (.var 0)]) (.members .string (NEFinset.of "a" ∅)) ()))
        (.refine .string (.members .string (NEFinset.of "b" ∅)) ()) = false := by
  decide

/-- **A certified union is separated**, which is the premise of `pairwiseCompat_of_separated`
    and of `admitsAtMostOne_of_separated`. -/
theorem separated_of_certAll {os : List Term} (h : certAll os = true) : Separated α os :=
  (pairwise_of_certAll h).imp separates_of_viewsDisjoint


end Calculus
