import Calculus.Dynamo.Lang.Term
import Calculus.Lang.Universe
import Calculus.Dynamo.Alg.Frontier
import Calculus.Dynamo.Alg.Opaque

/-!
# DynamoDB is a universe

DynamoDB supplies the facts of a universe that read no term: its primitive rows (`dynPrimAdm`),
its leaves (`dynLeaf`, `dynLeafMeet`), its shape classes (`dynShapes`) and the laws of `Ω`
(`Ω_topLaws`). Each primitive is one map at both orientations (`ground_selfdual`). The lemmas
here read the codecs and the literals of DynamoDB, and no term.
-/

namespace Calculus

open Alg (Orient)

/-- The DynamoDB primitive rows: `inBase` at a base and `inL` at a literal.

    The literal row is `inL`, with no `Numeral.WF` conjunct. `GroundKind.number.Carrier` is
    `WFNumeral`, so an alternative outside `D` has no representation. So membership is exact
    at every base, and `Adm_exact` covers the literal with nothing added. -/
instance dynPrimAdm : Alg.PrimAdm dynSyn where
  admV
    | .base k => inBase k
    | .literal k x => inL k x
  admV_exact
    | .base k, v => by
        show decide (v.member = k.member) = true ↔
          ((Alg.fiberCodec Attr.member k.member).f .host v).isSome = true
        rw [Alg.fiberCodec_isSome]
    | .literal k x, v => by
        show inL k x v = true ↔ ((groundCodec (.literal k x)).e v).isSome = true
        cases k <;> cases v <;>
          simp [literalCodec, inL, prism_rows, orient_rows]

/-- **Each DynamoDB primitive is one map at both orientations.** A primitive accepts a datum and
    changes nothing, so its read is its write. -/
theorem ground_selfdual : ∀ g, (groundCodec g).e = (groundCodec g).p := by
  intro g
  funext v
  cases g with
  | base k => cases k <;> cases v <;> rfl
  | literal k x => cases k <;> cases v <;> rfl

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

/-- **Two primitives apart share no value**, at the primitive rows. -/
theorem admV_prim_apart : ∀ g g' : Ground, Ground.apart g g' = true →
    ∀ v, (Alg.PrimAdm.admV (S := dynSyn) g v && Alg.PrimAdm.admV (S := dynSyn) g' v) = false
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

/-- The predicate leaves of DynamoDB hold together nowhere where they are apart. The store names
    no predicate but the truth, so no two stored predicates are apart. -/
instance dynLeafMeet : Alg.LeafMeet dynSig where
  predicates_apart
    | false, q, p, h, v => Pred.apart_sound q p h v
    | true, _, _, h, _ => nomatch h

/-! ## Inclusion lemmas, one per combinator -/

/-- A restriction of a restriction of `Ω` is a restriction of `Ω`. -/
theorem sub_restrict {c : Codec} (h : Sub c Ω) (q : Value → Bool) : Sub (c.restrict q) Ω :=
  Alg.sub_trans (sub_restrict_self c q) h

/-- **Each ground base is a restriction of `Ω`**: the identity on one fiber sends a datum only
    to itself. -/
theorem sub_baseCodec (k : GroundKind) : Sub (baseCodec k) Ω :=
  Alg.sub_fiberCodec Attr.member k.member

/-- A literal is a restriction of `Ω`, because a literal restricts its base. -/
theorem sub_literal (k : GroundKind) (x : k.Carrier) : Sub (literalCodec k x) Ω :=
  sub_restrict (sub_baseCodec k) (inL k x)

/-- `setAt` keeps an inclusion of graphs. -/
theorem setAt_sub {α : Type} {o : Alg.Orient} {c d : Codec} (h : Sub c d) {inj : α → Attr}
    {S : NEFinset α} {a : Attr} (he : setAt o c inj S = some a) : setAt o d inj S = some a := by
  rw [← setAt_congr (c := c) (fun x hx => by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (setAt_elem he x hx)
    rw [hy, h o _ _ hy])]
  exact he

/-- The image of a nonempty set under `some` is the set. -/
theorem neSetImage_id {α : Type} [DecidableEq α] (S : NEFinset α) :
    neSetImage (fun x => some x) S = some S := by
  refine neSetImage_eq_setImage.mpr (setImage_eq (fun _ _ => rfl)
    (fun _ _ _ _ _ h1 h2 => Option.some.inj (h1.trans h2.symm)) (fun y => ?_))
  simp

/-- **A codec that sends each element of a set to itself moves the set to itself**, at the
    set's own kind: every other kind misses. -/
theorem setAt_ident {o : Alg.Orient} {c : Codec} {k : SetKind} {S : NEFinset k.Carrier}
    (h : ∀ x ∈ S.1, c.f o (k.elem.into x) = some (k.elem.into x)) :
    setAt o c k.elem.into S = some (k.wire S) := by
  have hk : neSetImage (fun x => (c.f o (k.elem.into x)).bind k.elem.out) S = some S := by
    rw [neSetImage_congr (g := fun x => some x) fun x hx => by
      rw [h x hx]; exact k.elem.out_into x]
    exact neSetImage_id S
  obtain ⟨x₀, hx₀⟩ := S.2
  refine setAt_of (setAtK_eq.mpr ⟨S, hk, rfl⟩) fun k' hk' => ?_
  have hmiss : (c.f o (k.elem.into x₀)).bind k'.elem.out = none := by
    rw [h x₀ hx₀]; exact SetKind.elem_out_ne (Ne.symm hk') x₀
  unfold setAtK
  rw [neSetImage_none (setImage_none_of hx₀ hmiss)]
  rfl

/-- `Ω` moves a set to itself, at each orientation. -/
theorem setAt_Ω (o : Alg.Orient) (k : SetKind) (S : NEFinset k.Carrier) :
    setAt o Ω k.elem.into S = some (k.wire S) :=
  setAt_ident fun _ _ => rfl

/-- A set over a restriction of `Ω` is a restriction of `Ω`. -/
theorem sub_setCodec {c : Codec} (h : Sub c Ω) : Sub (setCodec c) Ω := fun o x y hc => by
  obtain ⟨k, S, rfl, hS⟩ := setCodec_f_eq.mp hc
  exact (setAt_Ω o k S).symm.trans (setAt_sub h hS)

/-! ## `opaque` is the identity, and the held-free fragment is self-dual

With one carrier, `Ω` sends each datum to itself, at both orientations. A lawful codec below `Ω`
can then only send a datum to itself, so it is a partial identity: an idempotent of the inverse
monoid of the carrier. Its write and its read are one map, and a fact of such a codec needs no
orientation. The direction of a codec lives in its adapters (`held`) and in its one-sided
decorations, not in its domain. -/

/-- **`opaque` is the identity at every orientation**: the read inverts the write. -/
theorem Ω_f (o : Alg.Orient) (x : Attr) : Ω.f o x = some x := rfl

/-- **A codec below `opaque` sends a datum only to itself**, at each orientation. -/
theorem sub_fix {c : Codec} (h : Sub c Ω) {o : Alg.Orient} {x y : Attr}
    (hc : c.f o x = some y) : y = x :=
  Option.some.inj ((h o x y hc).symm.trans (Ω_f o x))

/-! ## A set over a restriction of `Ω`, element by element

A restriction of `Ω` sends each element to itself (`sub_fix`). So a set over one writes and reads
exactly where each element does: the element map is injective and lands in one wire family by
construction. The meet's `set` row reads
these. -/

/-- **Over a restriction of `Ω`, a set moves exactly where every element does**, at each
    orientation. -/
theorem setCodec_isSome_of_sub {c : Codec} (h : Sub c Ω) (o : Alg.Orient) {k : SetKind}
    (S : NEFinset k.Carrier) :
    ((setCodec c).f o (k.wire S)).isSome = true ↔
      ∀ x ∈ S.1, (c.f o (k.elem.into x)).isSome = true := by
  refine ⟨fun he x hx => ?_, fun hall => ?_⟩
  · obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp he
    obtain ⟨k', S', hk, hS⟩ := setCodec_f_eq.mp ha
    cases k <;> cases k' <;> cases hk <;> exact setAt_elem hS x hx
  · have hid : ∀ x ∈ S.1, c.f o (k.elem.into x) = some (k.elem.into x) := fun x hx => by
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hall x hx)
      rw [ha, sub_fix h ha]
    exact Option.isSome_iff_exists.mpr ⟨_, setCodec_f_eq.mpr ⟨k, S, rfl, setAt_ident hid⟩⟩

/-- **A set over a restriction of `Ω` acts, at the orientation, where a set over a narrower
    element acts.** -/
theorem setCodec_mono (o : Alg.Orient) {c d : Codec} (hd : Sub d Ω)
    (h : ∀ w, (c.f o w).isSome = true → (d.f o w).isSome = true) (x : Attr)
    (hx : ((setCodec c).f o x).isSome = true) : ((setCodec d).f o x).isSome = true := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hx
  obtain ⟨k, S, rfl, hS⟩ := setCodec_f_eq.mp ha
  exact (setCodec_isSome_of_sub hd o S).mpr fun y hy => h _ (setAt_elem hS y hy)

/-- The laws of `Ω` that the held-free theory reads: each primitive is below `Ω`, `Ω` acts as the
    `arr` and `map` formers, and a set over a restriction of `Ω` is a restriction of `Ω` that acts
    where its element acts. The
    laws read no orientation, so one instance serves both. -/
instance Ω_topLaws (o : Alg.Orient) : Alg.TopLaws ⟨dynSig, o⟩ where
  ground
    | .base k => sub_baseCodec k
    | .literal k x => sub_literal k x
  set L hL c hc := by cases hL; exact sub_setCodec hc
  set_mono L hL o _ _ hd h := by cases hL; exact setCodec_mono o hd h

end Calculus
