import Calculus.Dynamo.Analysis.ScopeDisjoint
import Calculus.Lang.ScopeExact

/-!
# Exactness of disjointness at DynamoDB

The witness laws hold at DynamoDB. Two primitives that the leaf does not keep apart share the
datum of their base, or their literal. A set holds strings, numbers and bytes, so the set law
holds for the elements that are such primitives and unions of them: a datum that two such elements
share is an element of a one-element wire set.
-/

namespace Calculus

open Alg

/-- The kind of set that holds the elements of a base. -/
def GroundKind.setKind : GroundKind → Option SetKind
  | .string => some .string
  | .number => some .number
  | .binary => some .binary
  | _ => none

/-- **The primitives that a set holds**: a base or a literal of a string, a number or bytes. -/
def dynSetOk : Ground → Bool
  | .base k | .literal k _ => k.setKind.isSome

/-- A base with a kind of set stamps the member of that kind. -/
theorem GroundKind.member_of_setKind {k : GroundKind} {sk : SetKind} (h : k.setKind = some sk) :
    k.member = sk.member := by
  cases k <;> cases sk <;> first | rfl | exact nomatch h


/-- **A primitive that a set holds is the identity at its data**, and its data are of one kind of
    set. -/
theorem ground_set_id (o : Orient) {g : Ground} (hg : dynSetOk g = true) {u : Value}
    (h : ((Mean.ground (B := dynSig) g).f o u).isSome = true) :
    (Mean.ground (B := dynSig) g).f o u = some u ∧ ∃ sk : SetKind, u.member = sk.member := by
  cases g with
  | base k =>
    obtain ⟨sk, hsk⟩ := Option.isSome_iff_exists.mp hg
    have hf : (baseCodec k).f o u = if Attr.member u = k.member then some u else none := rfl
    change ((baseCodec k).f o u).isSome = true at h
    rw [hf] at h
    split at h
    · next hm =>
      exact ⟨by change (baseCodec k).f o u = _; rw [hf, if_pos hm],
        sk, by rw [hm]; exact GroundKind.member_of_setKind hsk⟩
    · exact nomatch h
  | literal k x =>
    obtain ⟨sk, hsk⟩ := Option.isSome_iff_exists.mp hg
    change ((literalCodec k x).f o u).isSome = true at h
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp h
    have hy' := (refine2_f (c := baseCodec k) (qV := inL k x) (qA := fun _ => true)).mp hy
    have hb : (baseCodec k).f o u = some y := hy'.2.1
    have hf : (baseCodec k).f o u = if Attr.member u = k.member then some u else none := rfl
    rw [hf] at hb
    split at hb
    · next hm =>
      cases hb
      exact ⟨hy, sk, by rw [hm]; exact GroundKind.member_of_setKind hsk⟩
    · exact nomatch hb


/-- **An element that a set holds is the identity at its data**, and its data are of one kind of
    set. -/
theorem setEl_id (o : Orient) {c : Mean.C dynSig} (hc : Scoped.SetEl (S := dynSyn) dynSetOk c) :
    ∀ u : Value, (c.f o u).isSome = true → c.f o u = some u ∧ ∃ sk : SetKind, u.member = sk.member := by
  refine hc.rec' (S := dynSyn) (fun c => ∀ u : Value, (c.f o u).isSome = true →
    c.f o u = some u ∧ ∃ sk : SetKind, u.member = sk.member)
    (fun g hg u h => ground_set_id o hg h) (fun cs μ ih u h => ?_)
  have hs : select cs (·.f o) u = (altCodec cs μ).f o u := rfl
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨c0, hfind, hrun⟩ := select_eq_some.mp (hs.trans hy)
  have hsome : (c0.f o u).isSome = true := by rw [hrun]; rfl
  obtain ⟨hid, hk⟩ := ih c0 (List.mem_of_find?_eq_some hfind) u hsome
  rw [hid] at hrun
  cases hrun
  exact ⟨hy, hk⟩

/-- A set moves where one kind moves it. -/
theorem setAt_isSome_ofK {α : Type} {o : Orient} {c : Codec} {inj : α → Attr} {S : NEFinset α}
    (k : SetKind) (hK : (setAtK o c inj S k).isSome = true) : (setAt o c inj S).isSome = true := by
  unfold setAt
  cases h1 : setAtK o c inj S .string with
  | some a => rfl
  | none =>
    cases h2 : setAtK o c inj S .number with
    | some a => rfl
    | none => cases k <;> simp_all

/-- A one-element set moves where the element moves to itself. -/
theorem setAt_single {α : Type} [DecidableEq α] {o : Orient} {c : Codec} {inj : α → Attr} (k : SetKind)
    (x : α) (y : k.Carrier) (h : (c.f o (inj x)).bind k.elem.out = some y) :
    (setAt o c inj (NEFinset.of x ∅)).isSome = true := by
  have hS : ∀ z ∈ (NEFinset.of x ∅).1, z = x := by
    intro z hz; simpa [NEFinset.of] using hz
  have himg : (setImage (fun z => (c.f o (inj z)).bind k.elem.out) (NEFinset.of x ∅).1).isSome = true :=
    setImage_isSome_of (fun z hz => by rw [hS z hz, h]; rfl)
      (fun x₁ h₁ x₂ h₂ _ _ _ => (hS x₁ h₁).trans (hS x₂ h₂).symm)
  apply setAt_isSome_ofK k
  unfold setAtK
  obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp himg
  rw [(neSetImage_eq_setImage (S := NEFinset.of x ∅) (T := ⟨T, setImage_nonempty hT
    (NEFinset.of x ∅).2⟩)).mpr hT]
  rfl


/-- **A codec that is the identity at a datum accepts the one-element set of the datum.** -/
theorem setCodec_accepts (o : Orient) (c : Codec) (sk : SetKind) (y : sk.Carrier)
    (h : c.f o (sk.elem.into y) = some (sk.elem.into y)) :
    ((setCodec c).f o (sk.wire (NEFinset.of y ∅))).isSome = true := by
  have key : (c.f o (sk.elem.into y)).bind sk.elem.out = some y := by
    rw [h]; exact sk.elem.out_into y
  cases sk <;> exact setAt_single _ y y key

/-- A base accepts exactly the data of its member. -/
theorem base_acc (o : Orient) (k : GroundKind) (v : Value) :
    ((Mean.ground (B := dynSig) (.base k)).f o v).isSome = decide (Attr.member v = k.member) :=
  fiberCodec_isSome Attr.member k.member o v

/-- A literal accepts the datum that it names. -/
theorem lit_acc (o : Orient) (k : GroundKind) (x : k.Carrier) :
    ((Mean.ground (B := dynSig) (.literal k x)).f o (k.prism.into x)).isSome = true := by
  have hh : ((groundCodec (.literal k x)).f .host (k.prism.into x)).isSome = true :=
    (PrimAdm.admV_exact (S := dynSyn) (.literal k x) _).mp (inL_iff.mpr rfl)
  have h1 := congrFun (ground_selfdual (.literal k x)) (k.prism.into x)
  simp only [Codec.e, Codec.p] at h1
  refine Orient.both
    (P := fun o => ((groundCodec (.literal k x)).f o (k.prism.into x)).isSome = true) hh ?_ o
  rw [← h1]; exact hh

/-- One datum of each base. -/
def baseWit : GroundKind → Value
  | .string => .str ""
  | .number => .num (WFNumeral.of "1")
  | .boolean => .bool true
  | .binary => .bin []
  | .null => .null

/-- The witness of a base is a datum of the member of the base. -/
theorem baseWit_member (k : GroundKind) : Attr.member (baseWit k) = k.member := by
  cases k <;> rfl

/-- **The primitive witness law holds at DynamoDB**, at each orientation. -/
theorem dynPWit (o : Orient) (g g' : Ground) (h : Leaf.primsApart (B := dynSig) g g' = false) :
    ∃ v, ((Mean.ground (B := dynSig) g).f o v).isSome = true ∧
      ((Mean.ground (B := dynSig) g').f o v).isSome = true := by
  change Ground.apart g g' = false at h
  match g, g', h with
  | .base k, .base k', h =>
    simp only [Ground.apart, Bool.not_eq_false', decide_eq_true_eq] at h
    subst h
    exact ⟨baseWit k', by rw [base_acc, baseWit_member]; simp,
      by rw [base_acc, baseWit_member]; simp⟩
  | .base k, .literal k' x, h =>
    simp only [Ground.apart, Bool.not_eq_false', decide_eq_true_eq] at h
    subst h
    exact ⟨k'.prism.into x, by rw [base_acc]; exact decide_eq_true (k'.summand.hμ x), lit_acc o k' x⟩
  | .literal k x, .base k', h =>
    simp only [Ground.apart, Bool.not_eq_false', decide_eq_true_eq] at h
    subst h
    exact ⟨k'.prism.into x, lit_acc o k' x, by rw [base_acc]; exact decide_eq_true (k'.summand.hμ x)⟩
  | .literal k x, .literal k' x', h =>
    simp only [Ground.apart] at h
    rcases (inferInstance : Decidable (k' = k)) with hk | hk
    · rw [dif_neg hk] at h; exact nomatch h
    · rw [dif_pos hk] at h
      subst hk
      simp only [Bool.not_eq_false', decide_eq_true_eq] at h
      subst h
      exact ⟨_, lit_acc o _ x, lit_acc o _ x⟩

/-- **The set law holds at DynamoDB** for the elements that a set holds: a datum that two such
    elements share is the element of a one-element wire set. -/
theorem dynWSet (o : Orient) (L : SetF Value Member Attr.member Attr.depth)
    (hL : Mean.set (B := dynSig) = some L) (c c' : Mean.C dynSig)
    (hc : Scoped.SetEl (S := dynSyn) dynSetOk c) (hc' : Scoped.SetEl (S := dynSyn) dynSetOk c')
    (hu : ∃ u, (c.f o u).isSome = true ∧ (c'.f o u).isSome = true) :
    ∃ v, ((L.lift c).f o v).isSome = true ∧ ((L.lift c').f o v).isSome = true := by
  have hLd : L = dSet := by
    have h : some dSet = some L := hL
    exact (Option.some.inj h).symm
  subst hLd
  obtain ⟨u, h1, h2⟩ := hu
  obtain ⟨hid, sk, hsk⟩ := setEl_id o hc u h1
  obtain ⟨hid', -⟩ := setEl_id o hc' u h2
  obtain ⟨y, hy⟩ := SetKind.out_of_member hsk
  have hu' : u = sk.elem.into y := sk.elem.into_out hy
  subst hu'
  exact ⟨sk.wire (NEFinset.of y ∅), setCodec_accepts o c sk y hid, setCodec_accepts o c' sk y hid'⟩

/-- **The witness laws hold at DynamoDB**, at each orientation. -/
theorem dynWLaws (o : Orient) : Scoped.WLaws dynSyn o dynSetOk where
  prim := dynPWit o
  set L hL c c' hc hc' hu := dynWSet o L hL c c' hc hc' hu


/-- **The decision is exact over the fragment at DynamoDB.** Two closed codecs whose entries are
    in the fragment share no datum, at one orientation and one table, exactly where the decision
    separates them. A fragment term is a primitive, a union, the bottom, a list, an object with no
    fill, or a set over primitives that a wire set holds. -/
theorem Closed.disjoint_exact {x y : Closed} (hx : ∀ i, Scoped.Frag (S := dynSyn) dynSetOk (x.scope.graph i) = true)
    (hy : ∀ j, Scoped.Frag (S := dynSyn) dynSetOk (y.scope.graph j) = true) (α : Table) (o : Orient) :
    x.disjoint y = true ↔ ∀ v : Value,
      (((x.meaning α).f o v).isSome && ((y.meaning α).f o v).isSome) = false :=
  Scoped.disjoint_exact (S := dynSyn) (dynLaws o) (dynWLaws o) hx hy

end Calculus
