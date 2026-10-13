import Calculus.Lang.Term

/-!
# The facts of a universe that read no term

A universe supplies its primitive rows (`PrimAdm`), its leaves (`Leaf`, `LeafMeet`), its shape
classes (`Shapes`) and the laws of its top (`TopLaws`). Each class reads the signature and its
meaning, and no term. The lemmas here read codecs only: the domain of a sum, of a list codec and of
the inclusion in the top, the held sets of the rules, and the unanimous member of a union.
-/

namespace Calculus.Alg

/-- A traversal succeeds at a cons exactly when the head and the tail do. -/
theorem traverse_cons_isSome {α β : Type} (f : α → Option β) (x : α) (xs : List α) :
    (traverse f (x :: xs)).isSome = ((f x).isSome && (traverse f xs).isSome) := by
  simp only [traverse]
  cases hx : f x <;> cases hxs : traverse f xs <;> simp

/-- **A sum acts exactly where one of its options acts.** -/
theorem select_isSome_attempt {V M X Y : Type} (os : List (Codec V M))
    (run : Codec V M → X → Option Y) (x : X) :
    (select os run x).isSome = true ↔ ∃ o ∈ os, (run o x).isSome = true := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨o, ho, -, he⟩ := select_admits ha
    exact ⟨o, ho, by rw [he]; rfl⟩
  · rintro ⟨o, ho, he⟩
    obtain ⟨o', hf⟩ := Option.isSome_iff_exists.mp
      (List.find?_isSome.mpr ⟨o, ho, he⟩ : (os.find? fun c => (run c x).isSome).isSome = true)
    unfold select; rw [hf]; exact List.find?_some (p := fun c => (run c x).isSome) hf

/-- **The list codec at an orientation**: read the prism, align, run each position at the
    orientation, and build with the prism. -/
theorem listCodec_f {V M : Type} {member : V → M} (sL : Summand (List V) V M member)
    (pre : List (Codec V M)) (sp : Option (Codec V M)) (suf : List (Codec V M)) :
    ∀ (o : Orient) (x : V), (listCodec sL pre sp suf).f o x =
      ((sL.p.out x).bind fun xs =>
        (alignL pre sp suf xs).bind (traverse fun cx => cx.1.f o cx.2)).map sL.p.into :=
  Orient.both (P := fun o => ∀ x, (listCodec sL pre sp suf).f o x =
      ((sL.p.out x).bind fun xs =>
        (alignL pre sp suf xs).bind (traverse fun cx => cx.1.f o cx.2)).map sL.p.into)
    (fun _ => rfl) (fun _ => rfl)

/-- **The value-side row of each primitive**, and its exactness. A universe supplies this class. -/
class PrimAdm (S : Syn) [Sem S] where
  /-- The values that a primitive writes. -/
  admV : S.Ground → S.V → Bool
  /-- The row is the domain of the primitive's codec at the orientation of the universe. -/
  admV_exact : ∀ g v, admV g v = true ↔ ((Syn.ground g).f S.o v).isSome = true

/-- **The leaves that a universe supplies.** The primitives and the predicates are the only part
    of a term that the test cannot read structurally. The leaves are facts of the signature at
    each absolute side, so the dual universe has the leaves of the universe. -/
class Leaf (B : Sig) where
  /-- Whether two primitives share no value. -/
  primsApart : B.Ground → B.Ground → Bool
  /-- Whether a predicate is data that the test can compare with another. -/
  isData : (s : Bool) → B.P s → Bool
  /-- Whether two predicates hold together nowhere. `false` says nothing: the test reads no more
      of a predicate than this answer. -/
  predicatesApart : (s : Bool) → B.P s → B.P s → Bool

/-- **The law of the predicate leaves**, at each absolute side: two predicates apart hold
    together nowhere. The law is a fact of the signature and its meaning, so the dual universe has
    the law of the universe. -/
class LeafMeet (B : Sig) [Mean B] [Leaf B] : Prop where
  predicates_apart : ∀ (s : Bool) (q p : B.P s), Leaf.predicatesApart s q p = true →
    ∀ x, (Mean.eval s q x && Mean.eval s p x) = false

/-! ## Apartness is antitone

Two domains are apart where no datum lies in both. A domain inside an apart domain is apart too,
so each soundness proof reads this fact where it would otherwise split the Booleans. -/

/-- **Apartness moves to a domain that lies inside.** -/
theorem apart_of_imp {x x' y : Bool} (h : x = true → x' = true) (h' : (x' && y) = false) :
    (x && y) = false := by
  cases x <;> cases y <;> first | rfl | (rw [h rfl] at h'; exact h')

/-- …on the right. -/
theorem apart_of_imp' {x y y' : Bool} (h : y = true → y' = true) (h' : (x && y') = false) :
    (x && y) = false := by
  cases x <;> cases y <;> first | rfl | (rw [h rfl] at h'; exact h')

/-- Two conjunctions are apart where their left conjuncts are, because each conjunction lies inside
    its conjunct. -/
theorem apart_and_left {a b c d : Bool} (h : (a && b) = false) : ((a && c) && (b && d)) = false :=
  apart_of_imp (fun hx => (Bool.and_eq_true_iff.mp hx).1)
    (apart_of_imp' (fun hy => (Bool.and_eq_true_iff.mp hy).1) h)

/-- …and where their right conjuncts are. -/
theorem apart_and_right {a b c d : Bool} (h : (c && d) = false) : ((a && c) && (b && d)) = false :=
  apart_of_imp (fun hx => (Bool.and_eq_true_iff.mp hx).2)
    (apart_of_imp' (fun hy => (Bool.and_eq_true_iff.mp hy).2) h)

/-- The four formers of the term language, as classes of root shapes. -/
inductive Former where
  | prim | set | list | object
deriving DecidableEq

/-- **The shape classes of a universe**: the former class of each datum, and the landing fact of
    each former of the signature. The carrier is one, so one class serves values and attributes,
    and each landing fact holds at each orientation. -/
class Shapes (S : Syn) [Sem S] where
  /-- The former class of a datum. -/
  former : S.V → Former
  /-- A primitive moves only primitive data. -/
  prim : ∀ o g v, ((Syn.ground g).f o v).isSome = true → former v = .prim
  /-- A set lift moves only set data. -/
  set : ∀ L, Mean.set (B := S.sig) = some L → ∀ c o v, ((L.lift c).f o v).isSome = true →
    former v = .set
  /-- The list prism builds list data. -/
  list : ∀ L, Mean.list (B := S.sig) = some L → ∀ vs, former (L.p.into vs) = .list
  /-- The map prism builds object data. -/
  map : ∀ F, Mean.map (B := S.sig) = some F → ∀ m, former (F.p.into m) = .object

/-! ## Inclusion lemmas, one per combinator -/

section Combinators
variable {V M : Type}

/-- Inclusion of graphs is transitive. -/
theorem sub_trans {c d u : Codec V M} (h : Sub c d) (h' : Sub d u) : Sub c u :=
  fun o x y hxy => h' o x y (h o x y hxy)

/-- A union of codecs below `u` is below `u`, because the selector returns the answer of one
    option. -/
theorem sub_altCodec {os : List (Codec V M)} {u : Codec V M} (h : ∀ o ∈ os, Sub o u)
    (μ : Option M) : Sub (altCodec os μ) u := fun o x y hxy =>
  let ⟨c, hc, _, hcy⟩ := altCodec_admits hxy
  h c hc o x y hcy

/-- A zipped traversal at the orientation `o` whose every row codec is below `u` is a traversal
    of `u` at `o`. -/
theorem forall₂_zip (o : Orient) {u : Codec V M} :
    ∀ (ds : List (Codec V M)) (xs : List (V)) (ys : List (V)),
    ds.length = xs.length → (∀ c ∈ ds, Sub c u) →
    List.Forall₂ (fun (cx : Codec V M × V) y => cx.1.f o cx.2 = some y) (ds.zip xs) ys →
    List.Forall₂ (fun x y => u.f o x = some y) xs ys
  | [], [], _, _, _, h => by cases h; exact .nil
  | d :: ds, x :: xs, y :: ys, hl, hd, .cons h1 h2 =>
      .cons ((hd d (by simp)) o _ _ h1)
        (forall₂_zip o ds xs ys (by simpa using hl) (fun c hc => hd c (by simp [hc])) h2)
  | [], _ :: _, _, hl, _, _ => nomatch hl
  | _ :: _, [], _, hl, _, _ => nomatch hl
  | _ :: _, _ :: _, [], _, _, h => nomatch h

/-- A list whose every slot is below a top that acts as the list former is below the top. -/
theorem sub_listCodec {member : V → M} {sL : Summand (List V) V M member} {u : Codec V M}
    (hu : ∀ o vs, u.f o (sL.p.into vs) = (traverse (u.f o) vs).map sL.p.into)
    {pre suf : List (Codec V M)} {sp : Option (Codec V M)}
    (hpre : ∀ c ∈ pre, Sub c u) (hsp : ∀ c ∈ sp, Sub c u) (hsuf : ∀ c ∈ suf, Sub c u) :
    Sub (listCodec sL pre sp suf) u := by
  have hrow : ∀ n ds, slotsL pre sp suf n = some ds → ∀ c ∈ ds, Sub c u := fun n ds h c hc => by
    rcases slotsL_mem pre sp suf n ds h c hc with h1 | h1 | h1
    · exact hpre c h1
    · exact hsp c h1
    · exact hsuf c h1
  intro o v a he
  obtain ⟨vs, as, hv, hE, rfl⟩ := carried_f.mp he
  simp only [alignL, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hE
  obtain ⟨ps, ⟨ds, hds, rfl⟩, ht⟩ := hE
  rw [sL.p.into_out hv, hu, traverse_eq_some.mpr (forall₂_zip o ds vs as
    (slotsL_length _ _ _ _ _ hds) (hrow _ _ hds) (traverse_eq_some.mp ht))]
  rfl

/-- An object with no fill whose every entry codec is below a top that acts as the map former
    is below the top. -/
theorem sub_objectCodec {member : V → M} {sM : Summand (MapOf V) V M member} {u : Codec V M}
    (hu : ∀ o (m : MapOf V), u.f o (sM.p.into m) =
      (funImage fun k => u.f o (m.get k)).map fun g => sM.p.into ⟨m.keys, g⟩)
    {sems : MapOf (FieldSem V M)} {rest : RestSem V M} (hnf : noFill sems = true)
    (hf : ∀ k, Sub (sems.2 k).codec u) (hw : ∀ c ∈ rcOf rest, Sub c u) :
    Sub (objectCodec sM sems rest) u := by
  intro o v a he
  obtain ⟨x, y, hv, hE, rfl⟩ := carried_f.mp he
  -- a present name: its entry goes through the top
  have hk : ∀ k : {k // k ∈ x.keys}, ∃ w, u.f o (x.get k) = some w ∧ y.at k.1 = some w := by
    intro k
    have h := objAt_at hE k.1
    rw [MapOf.at_of_mem k] at h
    simp only [liftTable, Option.map_eq_some_iff] at h
    obtain ⟨w, hcw, hyw⟩ := h
    obtain ⟨c, hc, hce⟩ := Option.bind_eq_some_iff.mp hcw
    exact ⟨w, (entryCodec_of (Q := fun c => Sub c u) hf hw hc) o _ _ hce, hyw.symm⟩
  have hs : ∀ k : {k // k ∈ x.keys}, (u.f o (x.get k)).isSome := fun k => by
    obtain ⟨w, hw', -⟩ := hk k; rw [hw']; rfl
  rw [sM.p.into_out hv, hu, funImage_eq (f := fun k => (u.f o (x.get k)).get (hs k))
    (fun k => (Option.some_get _).symm)]
  -- every other name is absent on both sides
  refine congrArg (fun m => some (sM.p.into m)) (MapOf.ext_at fun k => ?_)
  rcases Decidable.em (k ∈ x.keys) with hkx | hkx
  · obtain ⟨w, hw', hyw⟩ := hk ⟨k, hkx⟩
    rw [hyw]
    simp only [MapOf.at, dif_pos hkx, hw', Option.get_some]
  · have h := objAt_at hE k
    rw [MapOf.at_none hkx] at h
    rw [liftTable_none (noFill_at hnf k) h]
    simp only [MapOf.at, dif_neg hkx]

end Combinators

/-! ## The laws of the top -/

section Top
variable {S : Syn} [Sem S]
/-- The laws of the top that the held-free theory reads: each primitive is below the top, and
    the set lift keeps a codec below the top. The top is the identity, so it acts as the list
    and map formers with no law of the universe (`top_list`, `top_map`). -/
class TopLaws (S : Syn) [Sem S] : Prop where
  ground : ∀ g, Sub (Syn.ground g) (Syn.top (S := S))
  set : ∀ L ∈ Mean.set (B := S.sig), ∀ c : S.C, Sub c (Syn.top (S := S)) →
    Sub (L.lift c) (Syn.top (S := S))
  /-- A set over a restriction of the top acts, at each orientation, where a set over an element
      that acts less acts. The view of a set reads this law. -/
  set_mono : ∀ L ∈ Mean.set (B := S.sig), ∀ (o : Orient) (c d : S.C), Sub d (Syn.top (S := S)) →
    (∀ w, (c.f o w).isSome = true → (d.f o w).isSome = true) →
    ∀ x, ((L.lift c).f o x).isSome = true → ((L.lift d).f o x).isSome = true

/-- **The laws of the top read no orientation**, so the dual universe has the laws of the
    universe. -/
instance TopLaws.op [h : TopLaws S] : TopLaws S.op := ⟨h.ground, h.set, h.set_mono⟩

/-- The top acts as a list former: element by element. -/
theorem top_list {o : Orient} (into : List S.V → S.V) (vs : List S.V) :
    (Syn.top (S := S)).f o (into vs) = (traverse ((Syn.top (S := S)).f o) vs).map into :=
  (congrArg (Option.map into) (traverse_some vs)).symm

/-- The top acts as a map former: entry by entry. -/
theorem top_map {o : Orient} (into : MapOf S.V → S.V) (m : MapOf S.V) :
    (Syn.top (S := S)).f o (into m) =
      (funImage fun k => (Syn.top (S := S)).f o (m.get k)).map fun g => into ⟨m.keys, g⟩ :=
  (congrArg (Option.map fun g => into ⟨m.keys, g⟩) (funImage_eq (g := fun k => (Syn.top (S := S)).f o (m.get k))
    (fun _ => rfl))).symm

end Top

/-! ## Held sets -/

section Held
variable {V : Type}

/-- The positional part of `T₁ × … × Tₙ`, and of `… × T*` when a tail is present:
    the fixed head matched position by position, the tail uniformly. -/
def HTuple : List (V → Prop) → Option (V → Prop) → List V → Prop
  | [], none, vs => vs = []
  | [], some T, vs => ∀ x ∈ vs, T x
  | _ :: _, _, [] => False
  | T :: Ts, tl, v :: vs => T v ∧ HTuple Ts tl vs

/-- The positional part of a `list`'s held set: the suffix splits off the right end, and
    what is left is `HTuple`'s prefix-and-spread. `Forall₂` carries both the length of the
    suffix and the holding at each of its positions, so no length premise is owed. -/
def HTupleL (pre : List (V → Prop)) (sp : Option (V → Prop)) (suf : List (V → Prop)) (vs : List V) :
    Prop :=
  ∃ front back : List V,
    vs = front ++ back ∧ List.Forall₂ (fun T v => T v) suf back ∧ HTuple pre sp front

/-- `T₁ × … × Tₚ × T* × U₁ × … × U_s` (the rule `(list)`): the one positional held set, through the
    list prism of the universe. -/
def HList (pV : Ctor (List V) V) (pre : List (V → Prop)) (sp : Option (V → Prop))
    (suf : List (V → Prop)) : V → Prop :=
  fun v => ∃ vs, v = pV.into vs ∧ HTupleL pre sp suf vs

/-- `⟨n₁ :^π₁ T₁ … nₙ :^πₙ Tₙ⟩ ⊕ R(ρ)` (the rule `(object)`), through the map prism of the universe. A
    binding is `(required?, held set)`, and `R` is the held set of the open block. Every `req` name
    is present, and every present name is either declared, and holds its own set, or falls to the
    open block. -/
def HObject (mV : Ctor (MapOf V) V) (names : Finset String)
    (b : {k // k ∈ names} → Bool × (V → Prop)) (R : Option (V → Prop)) : V → Prop :=
  fun v => ∃ keys f, v = mV.into ⟨keys, f⟩ ∧
    (∀ k : {k // k ∈ names}, (b k).1 = true → k.1 ∈ keys) ∧
    (∀ k : {k // k ∈ keys},
      if h : k.1 ∈ names then (b ⟨k.1, h⟩).2 (f k)
      else ∃ T, R = some T ∧ T (f k))

/-- `⋃ Tᵢ` (the rule `(union)`). -/
def HUnion (Ts : List (V → Prop)) : V → Prop :=
  fun v => ∃ T ∈ Ts, T v

/-- The bottom's held set: nothing. It is disjoint from every held set. -/
def HNever : V → Prop := fun _ => False

end Held

/-- A unanimous member is the member of every option. -/
theorem unanimous_spec {M : Type} [DecidableEq M] : ∀ {l : List (Option M)} {m},
    unanimous l = some m → ∀ x ∈ l, x = some m
  | [], _, h => nomatch h
  | μ :: μs, m, h => by
      replace h : (if μs.all (· == μ) then μ else none) = some m := h
      cases hall : μs.all (· == μ) with
      | false => rw [hall] at h; exact nomatch h
      | true =>
        rw [hall] at h
        replace h : μ = some m := h
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact h
        · have hbe := List.all_eq_true.mp hall x hx'
          have hxeq : x = μ := eq_of_beq hbe
          rw [hxeq, h]

end Calculus.Alg
