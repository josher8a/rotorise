import Calculus.Lang.ScopeDisjoint

/-!
# Compatibility over the graph of a closed codec

`Scoped.compat` decides one half of the compatibility of two closed codecs: at the orientation, two
maps that answer at one input give one output. The decision reads the flat graph of each closed
codec, with one row per operation of the left operand. Each row is one of two warrants: the two
terms share no datum there, or both lie below the top. The walk is the walk of `Scoped.disjoint`
with the row of agreement (`rowSpecC`). Below a guard, the walk assumes a pair of entries while it
compares the two bodies, and it reads any other pair at the same fuel (`pairX`). A fuel bounds the
walk, and an empty fuel answers `false`.

`Scoped.compat_sound` states the soundness against `Closed.meaning`. The pairs that the walk visits
form one relation (`Vis`), and the relation is post-fixed up to the unfolding of two entries
(`vis_postW`). The proof is a rule induction on the derivation of the left answer (`Eval`), with
no fuel, no table and no step index. A container reads its positions one layer down, so the proof
cuts each position at the depth (`trunc`) and reads the container through the law of the step. A
`held` reads the derivation of its inner term at each input: the inner term has no leaf. The rows
that read no structure call the walk of `Scoped.disjoint`, on the terms and on their views.
-/

namespace Calculus.Alg.Scoped

variable {B : Sig}

/-! ## The rows -/

section Rows
variable [Mean B] [Leaf B] {NL NR : Nat} (sL : Fin NL → Graph B NL) (sR : Fin NR → Graph B NR)
  (o : Orient)

/-- **The term inside which a `held` acts at the orientation**: its outer term where its side is
    the caller side of the orientation, and its inner term otherwise. Any other term is its own. -/
def heldIn {N : Nat} : Graph B N → Graph B N
  | .node (.held s _ _) a => bif o.c == s then heldIn (a false) else heldIn (a true)
  | t => t

/-- Whether a graph term is the bottom. -/
def isNeverG {N : Nat} : Graph B N → Bool
  | .node .never _ => true
  | _ => false

/-- **The rows that read no structure**: the bottom, two terms below the top, two terms that the
    walk of `disjoint` separates, the two terms inside which their `held`s act, and the two views
    at the orientation. -/
def cbaseG (x : Graph B NL) (y : Graph B NR) : Bool :=
  isNeverG x || isNeverG y || (belowTop sL x && belowTop sR y) ||
    decG sL sR (fuel NL NR) [] x y ||
    decG sL sR (fuel NL NR) [] (heldIn o x) (heldIn o y) ||
    decG (viewSys sL o) (viewSys sR o) (fuel NL NR) [] (viewG sL o x)
      (viewG sR o y)

/-- **Two slots answer alike at absence** where the orientation fills: a fill beside a required
    slot, and no other slot beside a fill. Two fills are refused, because the constants have no
    decidable equality. -/
def absentAgreeG : SlotMode B → SlotMode B → Bool
  | .fill _, .req | .req, .fill _ => true
  | .fill _, _ | _, .fill _ => false
  | _, _ => true

/-- The open block of an object node as a term: the bottom where the object has no block. -/
def blockG {N : Nat} {fs : Finset String} {md : {x // x ∈ fs} → SlotMode B} :
    (s : Fin 2) → ((TOp.obj fs md s).Pos → Graph B N) → Graph B N
  | ⟨0, _⟩, _ => Graph.never
  | ⟨1, _⟩, a => a (.inr ⟨0, Nat.one_pos⟩)

/-- The test of the open block of a left object, at the position. -/
def blockK {fs : Finset String} {md : {x // x ∈ fs} → SlotMode B} :
    (w : Fin 2) → ((TOp.obj fs md w).Pos → Graph B NR → Bool) → Graph B NR → Bool
  | ⟨0, _⟩, _ => fun _ => true
  | ⟨1, _⟩, g => g (.inr ⟨0, Nat.one_pos⟩)

/-- The test of the slot that a left object gives one name, at the position. -/
def slotK {fs : Finset String} {md : {x // x ∈ fs} → SlotMode B} {s : Fin 2}
    (kid : (TOp.obj fs md s).Pos → Graph B NR → Bool) (k : String) : Graph B NR → Bool :=
  if h : k ∈ fs then kid (.inl ⟨k, h⟩) else match s with
    | ⟨0, _⟩ => fun _ => true
    | ⟨1, _⟩ => kid (.inr ⟨0, Nat.one_pos⟩)

variable {sL sR}

/-- **Two objects agree** where the two slots at each declared name agree and answer alike at
    absence, and where the two open blocks agree. `kid` is the test of a position of the left
    object below a guard. -/
def objK {fs : Finset String} {md : {x // x ∈ fs} → SlotMode B} {s : Fin 2}
    (a : (TOp.obj fs md s).Pos → Graph B NL)
    (kid : (TOp.obj fs md s).Pos → Graph B NR → Bool) : Graph B NR → Bool
  | .node (.obj fs' md' s') b =>
      (keyPos fs).all (fun x => (!o.c || absentAgreeG (md x) (slotAtG (md := md') b x.1).1) &&
        kid (.inl x) (slotAtG (md := md') b x.1).2) &&
      (keyPos fs').all (fun x => (!o.c || absentAgreeG (slotAtG (md := md) a x.1).1 (md' x)) &&
        slotK kid x.1 (b (.inl x))) &&
      blockK (md := md) s kid (blockG (md := md') s' b)
  | _ => false

/-- **The family of a guarded left node beside a node of its class**: the inner terms of two
    `held`s, the element of two sets, two lists, and two objects. Two lists read the aligned rows
    at each common length (`alignedRows`), and each position is read at the test `kid` below a
    guard. Any other pair has no family. -/
def famN : (op : TOp B) → (op.Pos → Graph B NL) → (op.Pos → Graph B NR → Bool) →
    Graph B NR → Bool
  | .held s k₀ ks, _, kid, .node (.held s' k₀' ks') b =>
      decide ((⟨s, k₀ :: ks⟩ : (s : Bool) × List (B.G s × Bool)) = ⟨s', k₀' :: ks'⟩) && kid true (b true)
  | .set, _, kid, .node .set b => kid () (b ())
  | .list n s m, _, kid, .node (.list n' s' m') b =>
      alignedAll (allZipT kid) (listPartsX (B := B) (a := n) (s := s) (b := m) fun p => p).1
        (listPartsX (B := B) (a := n) (s := s) (b := m) fun p => p).2.1
        (listPartsX (B := B) (a := n) (s := s) (b := m) fun p => p).2.2
        (listParts b).1 (listParts b).2.1 (listParts b).2.2
  | .obj _ md _, a, kid, y => objK (md := md) o a kid y
  | _, _, _, _ => false

omit [Mean B] [Leaf B] in
/-- **Two positions that are one entry**: a left entry beside a right entry that the
    identification `ι` names. An identification names a pair of entries with one meaning, so the
    pair agrees by reflexivity. Two scopes have no entry in common (`twoScopes`), and one scope
    names each entry once (`oneScope`). -/
def oneG (ι : Fin NL → Fin NR → Bool) (i : Fin NL) : Graph B NR → Bool
  | .leaf j => ι i j
  | _ => false

variable (sL sR)

/-- **The row of agreement**, one case for each operation of the left operand. An entry agrees
    with the entry that the identification `ι` names as the same entry. -/
def rowSpecC (ι : Fin NL → Fin NR → Bool) : Row sL sR where
  leaf rs j y := (cbaseG sL sR o (.leaf j) y || oneG ι j y) || rs (sL j) y
  node rs op a self kid y := match op, a, self, kid with
    | .never, _, _, _ => true
    | .refine q qA, a, self, _ => cbaseG sL sR o (.node (.refine q qA) a) y || self () y
    | .union m, a, self, _ => cbaseG sL sR o (.node (.union m) a) y ||
        (List.finRange m).all fun p => self p y
    | op, a, _, kid => rightC sR (rs (.node op a))
        (fun y' => cbaseG sL sR o (.node op a) y' || famN o op a kid y') y

/-- **The walk at a fuel**, the walk of the row of agreement. -/
def compG (ι : Fin NL → Fin NR → Bool) : Nat → Tbl NL NR → Graph B NL → Graph B NR → Bool :=
  walk (rowSpecC sL sR o ι)

end Rows

/-- **Two scopes identify no entry.** The decision reads two closed codecs as two scopes. -/
def twoScopes {NL NR : Nat} : Fin NL → Fin NR → Bool := fun _ _ => false

/-- **One scope identifies each entry with itself**, by the index of the entry. -/
def oneScope {N : Nat} : Fin N → Fin N → Bool := fun i j => decide (i = j)

/-- **One half of the compatibility of two closed codecs**, at their roots and at the orientation,
    under the identification `ι` of their entries. The fuel is the fuel of `disjoint`. -/
def compat [Mean B] [Leaf B] {NL NR : Nat} (o : Orient) (ι : Fin NL → Fin NR → Bool)
    (dL : Closed B NL) (rL : Fin NL) (dR : Closed B NR) (rR : Fin NR) : Bool :=
  compG dL.graph dR.graph o ι (fuel NL NR) [] (.leaf rL) (.leaf rR)

/-- **The compatibility of two closed codecs**: both halves, at the host and at the dual. -/
def compatPair [Mean B] [Leaf B] {NL NR : Nat} (ι : Fin NL → Fin NR → Bool) (dL : Closed B NL)
    (rL : Fin NL) (dR : Closed B NR) (rR : Fin NR) : Bool :=
  compat .host ι dL rL dR rR && compat .dual ι dL rL dR rR

/-- **A root of one scope agrees with itself**: the row of one entry answers at the root, before
    the walk reads a body. -/
theorem compatPair_oneScope [Mean B] [Leaf B] {N : Nat} (d : Closed B N) (r : Fin N) :
    compatPair oneScope d r d r = true := by
  have hn : fuel N N = (fuel N N - 1) + 1 :=
    (Nat.succ_pred_eq_of_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))).symm
  have half : ∀ o, compat o oneScope d r d r = true := by
    intro o
    simp only [compat, compG]
    rw [hn]
    simp only [walk, goW, rowSpecC, oneG, oneScope, decide_true, Bool.or_true, Bool.true_or]
  simp only [compatPair, half, Bool.and_self]

/-! ## A term with no leaf below a wall -/

section Good
variable {B : Sig}

/-- No leaf below a wall. -/
def Good {N : Nat} (t : Graph B N) : Prop := ∀ j, t.wlv (TSig B) j = false

/-- Each child of a node that is not a wall keeps no leaf below a wall. -/
theorem good_child {N : Nat} {op : TOp B} {a : op.Pos → Graph B N} (h : Good (.node op a))
    (hk : TOp.kind op ≠ .wall) (p : op.Pos) : Good (a p) :=
  fun j => Bool.eq_false_iff.mpr fun h' =>
    Bool.false_ne_true ((h j).symm.trans (Flat.wlv_node.mpr (Or.inr ⟨hk, p, h'⟩)))

/-- Each child of a wall with no leaf below the wall has no leaf. -/
theorem noLeaf_wall {N : Nat} {op : TOp B} {a : op.Pos → Graph B N} (h : Good (.node op a))
    (hk : TOp.kind op = .wall) (p : op.Pos) : NoLeaf (a p) :=
  fun j => Bool.eq_false_iff.mpr fun h' =>
    Bool.false_ne_true ((h j).symm.trans (Flat.wlv_node.mpr (Or.inl ⟨hk, p, h'⟩)))

/-- A term with no leaf has no leaf below a wall. -/
theorem good_of_noLeaf {N : Nat} : ∀ {t : Graph B N}, NoLeaf t → Good t
  | .leaf _, _ => fun _ => rfl
  | .node _ _, h => fun j => Bool.eq_false_iff.mpr fun h' => by
    rcases Flat.wlv_node.mp h' with ⟨_, p, hp⟩ | ⟨_, p, hp⟩
    · exact Bool.false_ne_true ((noLeaf_child h p j).symm.trans hp)
    · exact Bool.false_ne_true ((good_of_noLeaf (noLeaf_child h p) j).symm.trans hp)

/-- The tail of a union keeps no leaf below a wall. -/
theorem good_tail {N m : Nat} {a : Fin (m + 1) → Graph B N} (h : Good (.node (TOp.union (m + 1)) a)) :
    Good (.node (TOp.union m) fun p : Fin m => a p.succ) :=
  fun j => Bool.eq_false_iff.mpr fun h' => by
    rcases Flat.wlv_node.mp h' with ⟨hk, _⟩ | ⟨_, p, hp⟩
    · exact nomatch hk
    · exact Bool.false_ne_true ((good_child h (fun hk => nomatch hk) p.succ j).symm.trans hp)

/-- **Each entry of the graph of a closed codec has no leaf below a wall.** -/
theorem Closed.good_graph {N : Nat} (d : Closed B N) (i : Fin N) : Good (d.graph i) :=
  fun _ => Bool.eq_false_iff.mpr fun h => SFlat.wlv_inl (d i) (fun l => l) (fun l => Fin.castLE _ l) h

end Good

/-! ## Soundness -/

section Sound
variable {S : Syn} [Sem S] {τ : (s : Bool) → TableAt S.sig s} {o : Orient}

variable (o) in
/-- **Agreement below a depth**: two maps at the orientation that answer at one input of a smaller
    depth give one output. -/
def AgB (k : Nat) (c c' : Mean.C S.sig) : Prop :=
  ∀ x, Mean.d (B := S.sig) x < k → ∀ y z, c.f o x = some y → c'.f o x = some z → y = z

/-- Two codecs that agree below one more depth give two cut codecs that agree. -/
theorem agree_trunc {j : Nat} {c c' : Mean.C S.sig} (h : AgB o (j + 1) c c') :
    Agree o (trunc j c) (trunc j c') :=
  PW.trunc (Φ := fun a b => ∀ y z, a = some y → b = some z → y = z) (fun _ _ h => nomatch h) h

/-- **A container agrees below one more depth** where its positions, cut at the depth, give two
    agreeing containers: the step reads the positions of a container one layer down. -/
theorem AgB.down {op op' : TOp S.sig} (hk : op.kind = .down) (hk' : op'.kind = .down)
    {a : op.Pos → Mean.C S.sig} {b : op'.Pos → Mean.C S.sig} {j : Nat}
    (h : Agree o (TOp.run τ op fun p => trunc j (a p)) (TOp.run τ op' fun q => trunc j (b q))) :
    AgB o (j + 2) (TOp.run τ op a) (TOp.run τ op' b) :=
  PW.down (Φ := fun a b => ∀ y z, a = some y → b = some z → y = z) hk hk' fun v => h v

omit [Sem S] in
/-- A codec at a position of a list shape is the codec of one position. -/
theorem mem_listSlots {X : Type} {n m : Nat} {s : Fin 2} (a : (TOp.list n s m (B := S.sig)).Pos → X)
    {c : X} (h : c ∈ List.ofFn (fun p => a (.inl p)) ∨ optOf s (fun p => a (.inr (.inl p))) = some c ∨
      c ∈ List.ofFn (fun p => a (.inr (.inr p)))) : ∃ p, a p = c := by
  rcases h with h | h | h
  · obtain ⟨p, rfl⟩ := List.mem_ofFn.mp h; exact ⟨_, rfl⟩
  · obtain ⟨p, hp⟩ := optOf_mem s _ c h; exact ⟨_, hp⟩
  · obtain ⟨p, rfl⟩ := List.mem_ofFn.mp h; exact ⟨_, rfl⟩

omit [Sem S] in
/-- The codec row of a list node is the map of the position row through the codecs of the
    positions. -/
theorem rowOfG_listPartsX {X : Type} {n m : Nat} {s : Fin 2}
    (g : (TOp.list n s m (B := S.sig)).Pos → X) (k : Nat) :
    rowOfG (listPartsX g).1 (listPartsX g).2.1 (listPartsX g).2.2 k =
      (rowOfG (listPartsX (B := S.sig) (a := n) (s := s) (b := m) fun p => p).1
        (listPartsX (B := S.sig) (a := n) (s := s) (b := m) fun p => p).2.1
        (listPartsX (B := S.sig) (a := n) (s := s) (b := m) fun p => p).2.2 k).map (List.map g) := by
  rw [← rowOfG_map]
  have e1 : (List.ofFn fun p : Fin n => g (Sum.inl p)) =
      List.map g (List.ofFn fun p : Fin n => (Sum.inl p : (TOp.list n s m (B := S.sig)).Pos)) :=
    List.map_ofFn.symm
  have e2 : (List.ofFn fun p : Fin m => g (Sum.inr (Sum.inr p))) =
      List.map g (List.ofFn fun p : Fin m =>
        (Sum.inr (Sum.inr p) : (TOp.list n s m (B := S.sig)).Pos)) :=
    List.map_ofFn.symm
  simp only [listPartsX, e1, e2]
  rw [optOf_mapX g s (fun p => Sum.inr (Sum.inl p))]

/-- **Two lists agree** where the positions of the two shapes agree at each common length. -/
theorem agree_runList {n m n' m' : Nat} {s s' : Fin 2}
    {a : (TOp.list n s m (B := S.sig)).Pos → Mean.C S.sig}
    {b : (TOp.list n' s' m' (B := S.sig)).Pos → Mean.C S.sig}
    (h : ∀ k r₁ r₂, rowOfG (listPartsX a).1 (listPartsX a).2.1 (listPartsX a).2.2 k = some r₁ →
      rowOfG (listPartsX b).1 (listPartsX b).2.1 (listPartsX b).2.2 k = some r₂ →
      List.Forall₂ (Agree o) r₁ r₂) :
    Agree o (TOp.run τ (.list n s m) a) (TOp.run τ (.list n' s' m') b) := by
  simp only [TOp.run]
  split
  · next L _ =>
    refine agree_list fun k ds ds' hd hd' => h k ds ds' ?_ ?_
    · rw [slotsL_eq_rowOfG] at hd; exact hd
    · rw [slotsL_eq_rowOfG] at hd'; exact hd'
  · exact agree_empty_left _ _

/-! ### The rows that read no structure -/

/-- **A `held` acts at an orientation only inside the term where its half sits**: the domain of a
    term lies inside the domain of `heldIn`. -/
theorem heldIn_dom {N : Nat} (d : GSys τ N) (t : Graph S.sig N) :
    ∀ x : Mean.V (B := S.sig),
      ((mng τ d t).f o x).isSome = true → ((mng τ d (heldIn o t)).f o x).isSome = true := by
  induction t with
  | leaf _ => exact fun _ h => h
  | node op a ih =>
    intro x h
    cases op with
    | held s k₀ ks =>
      have h' : ((held1 s (mng τ d (a true)) (mng τ d (a false))
          ((τ s).word (k₀ :: ks))).f o x).isSome = true := h
      rw [held1_f_isSome, Bool.and_eq_true] at h'
      -- by the four cases: the lemmas of a lawful BEq reach the choice axiom through an order instance
      have hne : ∀ a b : Bool, (a == b) = false → a ≠ b
        | false, false, h, _ | true, true, h, _ => nomatch h
      have heq : ∀ a b : Bool, (a == b) = true → a = b
        | false, false, _ | true, true, _ => rfl
        | false, true, h | true, false, h => nomatch h
      simp only [heldIn]
      cases hs : (o.c == s)
      · rw [PairAt.one_ne _ _ _ (hne _ _ hs)] at h'
        exact ih true x (gate_isSome h'.2)
      · obtain rfl := heq _ _ hs
        rw [bne, hs, Bool.not_true, Bool.false_or] at h'
        exact ih false x h'.1
    | prim _ | opaq | never | set | list _ _ _ | refine _ _ | legacy _ | obj _ _ _ | union _ =>
      simpa only [heldIn] using h

/-- The bottom accepts nothing. -/
theorem none_of_isNeverG {N : Nat} (d : GSys τ N) :
    ∀ (t : Graph S.sig N), isNeverG t = true → ∀ x, (mng τ d t).f o x = none
  | .leaf _, h => nomatch h
  | .node op _, h => by
    cases op with
    | never => exact fun _ => rfl
    | prim _ | opaq | set | list _ _ _ | refine _ _ | held _ _ _ | legacy _ | obj _ _ _ | union _ =>
      exact nomatch h

variable [Leaf S.sig] [Shapes S] [TopLaws S]

/-- **Two terms whose views the walk separates share no datum**: each view admits what its term
    admits. -/
theorem apart_of_views (laws : Laws S o) {NL NR : Nat} (cL : Closed S.sig NL) (cR : Closed S.sig NR)
    {n : Nat} {x : Graph S.sig NL} {y : Graph S.sig NR}
    (h : decG (viewSys cL.graph o) (viewSys cR.graph o) n [] (viewG cL.graph o x)
      (viewG cR.graph o y) = true) :
    ∀ v, (((mng τ (Closed.toG τ cL) x).f o v).isSome &&
      ((mng τ (Closed.toG τ cR) y).f o v).isSome) = false := by
  intro v
  have hap := decG_sound (Closed.viewToG τ o cL) (Closed.viewToG τ o cR) laws h v
  cases h1 : ((mng τ (Closed.toG τ cL) x).f o v).isSome
  · rfl
  cases h2 : ((mng τ (Closed.toG τ cR) y).f o v).isSome
  · rfl
  have e1 := lem_all cL x (Mean.d (B := S.sig) v) (fun j _ => view_entries cL _ j) v (Nat.le_refl _) h1
  have e2 := lem_all cR y (Mean.d (B := S.sig) v) (fun j _ => view_entries cR _ j) v (Nat.le_refl _) h2
  rw [e1, e2] at hap
  exact nomatch hap

/-- **The rows that read no structure are sound**: they give agreement at every depth. -/
theorem cbaseG_sound (laws : Laws S o) {NL NR : Nat} (cL : Closed S.sig NL) (cR : Closed S.sig NR)
    {x : Graph S.sig NL} {y : Graph S.sig NR} (h : cbaseG cL.graph cR.graph o x y = true) :
    Agree o (mng τ (Closed.toG τ cL) x) (mng τ (Closed.toG τ cR) y) := by
  simp only [cbaseG, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with (((((hx | hy) | ⟨hx, hy⟩) | hd) | hh) | hv)
  · intro v y₁ z₁ h₁ _
    rw [none_of_isNeverG (Closed.toG τ cL) x hx v] at h₁
    exact nomatch h₁
  · intro v y₁ z₁ _ h₂
    rw [none_of_isNeverG (Closed.toG τ cR) y hy v] at h₂
    exact nomatch h₂
  · exact agree_bound (sub_of_belowTop (Closed.toG τ cL) hx) (sub_of_belowTop (Closed.toG τ cR) hy)
  · exact agree_apart (decG_sound (Closed.toG τ cL) (Closed.toG τ cR) laws hd)
  · exact agree_apart fun v => apart_of_imp (heldIn_dom (Closed.toG τ cL) x v)
      (apart_of_imp' (heldIn_dom (Closed.toG τ cR) y v)
        (decG_sound (Closed.toG τ cL) (Closed.toG τ cR) laws hh v))
  · exact agree_apart (apart_of_views laws cL cR hv)

variable {NL NR : Nat}

/-! ### The object row -/

omit [Leaf S.sig] [Shapes S] [TopLaws S] in
/-- **The entry of an object node at a name is the term of its slot**, and an undeclared name with
    an entry reads the open block. -/
theorem entry_of_slot {N : Nat} (φ : Graph S.sig N → Mean.C S.sig) {fs : Finset String}
    {md : {x // x ∈ fs} → SlotMode S.sig} {s : Fin 2} (a : (TOp.obj fs md s).Pos → Graph S.sig N)
    (n : String) {c : Mean.C S.sig}
    (h : entryCodec ⟨fs, fun x => mkField (md x) (φ (a (.inl x)))⟩
      (rcOf (restOf s fun p => φ (a (.inr p)))) n = some c) :
    c = φ (slotAtG (md := md) a n).2 ∧
      (n ∉ fs → (slotAtG (md := md) a n).2 = blockG (md := md) s a ∧ s.val ≠ 0) := by
  unfold entryCodec at h
  unfold slotAtG
  rcases Decidable.em (n ∈ fs) with hn | hn
  · rw [MapOf.at_of_mem (m := ⟨fs, _⟩) ⟨n, hn⟩] at h
    rw [dif_pos hn]
    refine ⟨?_, fun h' => absurd hn h'⟩
    rw [← Option.some.inj h, fieldCodec_mkField]
  · rw [MapOf.at_none (m := ⟨fs, _⟩) hn] at h
    rw [dif_neg hn]
    match s, a, h with
    | ⟨0, _⟩, _, h => exact nomatch h
    | ⟨1, _⟩, _, h => exact ⟨(Option.some.inj h).symm, fun _ => ⟨rfl, Nat.one_ne_zero⟩⟩

omit [Leaf S.sig] [Shapes S] [TopLaws S] in
/-- **A name acts at absence as its slot does**: a declared name as its declared slot, and an
    undeclared name as an `optional` slot. -/
theorem absentOf_slot {N : Nat} {fs : Finset String} {md : {x // x ∈ fs} → SlotMode S.sig}
    {s : Fin 2} (a : (TOp.obj fs md s).Pos → Graph S.sig N) (c : {x // x ∈ fs} → Mean.C S.sig)
    (c₀ : Mean.C S.sig) (n : String) :
    absentOf o ((⟨fs, fun x => mkField (md x) (c x)⟩ : MapOf _).at n) =
      absentOf o (some (mkField (slotAtG (md := md) a n).1 c₀)) := by
  unfold slotAtG
  rcases Decidable.em (n ∈ fs) with hn | hn
  · rw [MapOf.at_of_mem (m := ⟨fs, _⟩) ⟨n, hn⟩, dif_pos hn]
    show absentOf o (some (mkField (md ⟨n, hn⟩) (c ⟨n, hn⟩))) =
      absentOf o (some (mkField (md ⟨n, hn⟩) c₀))
    cases md ⟨n, hn⟩ <;> rfl
  · rw [MapOf.at_none (m := ⟨fs, _⟩) hn, dif_neg hn]
    rfl

omit [Leaf S.sig] [Shapes S] [TopLaws S] in
/-- **Two slots that `absentAgreeG` admits answer alike at absence.** -/
theorem absentAgree_sound {m m' : SlotMode S.sig} {c c' : Mean.C S.sig} {y₁ y₂ : Option (Mean.V (B := S.sig))}
    (h : (!o.c || absentAgreeG m m') = true) (e1 : absentOf o (some (mkField m c)) = some y₁)
    (e2 : absentOf o (some (mkField m' c')) = some y₂) : y₁ = y₂ := by
  cases hc : o.c <;> cases m <;> cases m' <;>
    simp only [absentOf, mkField, hc, cond_true, cond_false, Option.some.injEq, reduceCtorEq,
      absentAgreeG, Bool.not_true, Bool.not_false, Bool.true_or, Bool.false_or] at h e1 e2 <;>
    exact e1.symm.trans e2

omit [Sem S] [Leaf S.sig] [Shapes S] [TopLaws S] in
/-- A slot of an object node is the bottom or a child. -/
theorem slot_mem {N : Nat} {fs : Finset String} {md : {x // x ∈ fs} → SlotMode S.sig} {s : Fin 2}
    (a : (TOp.obj fs md s).Pos → Graph S.sig N) (n : String) :
    (slotAtG (md := md) a n).2 = Graph.never ∨ ∃ p, a p = (slotAtG (md := md) a n).2 := by
  unfold slotAtG
  rcases Decidable.em (n ∈ fs) with hn | hn
  · rw [dif_pos hn]; exact Or.inr ⟨_, rfl⟩
  · rw [dif_neg hn]
    match s, a with
    | ⟨0, _⟩, _ => exact Or.inl rfl
    | ⟨1, _⟩, _ => exact Or.inr ⟨_, rfl⟩

omit [Sem S] [Leaf S.sig] [Shapes S] [TopLaws S] in
/-- The open block of an object node is the bottom or a child. -/
theorem block_mem {N : Nat} {fs : Finset String} {md : {x // x ∈ fs} → SlotMode S.sig} :
    ∀ (s : Fin 2) (a : (TOp.obj fs md s).Pos → Graph S.sig N),
      blockG (md := md) s a = Graph.never ∨ ∃ p, a p = blockG (md := md) s a
  | ⟨0, _⟩, _ => Or.inl rfl
  | ⟨1, _⟩, _ => Or.inr ⟨_, rfl⟩

omit [Leaf S.sig] [Shapes S] [TopLaws S] in
/-- A slot that `slotK` tests agrees: the slot of a left object at a name, against a term. -/
theorem slotK_agree {N N' : Nat} (φL : Graph S.sig N → Mean.C S.sig) (φR : Graph S.sig N' → Mean.C S.sig)
    {Rc : Graph S.sig N → Graph S.sig N' → Bool} {fs : Finset String}
    {md : {x // x ∈ fs} → SlotMode S.sig} {s : Fin 2} (a : (TOp.obj fs md s).Pos → Graph S.sig N)
    (hpair : ∀ p u, Rc (a p) u = true → Agree o (φL (a p)) (φR u))
    (hnev : ∀ u, Agree o (φL Graph.never) (φR u)) (n : String) (u : Graph S.sig N')
    (h : slotK (fun p => Rc (a p)) n u = true) : Agree o (φL (slotAtG (md := md) a n).2) (φR u) := by
  rcases Decidable.em (n ∈ fs) with hn | hn
  · simp only [slotK, slotAtG, dif_pos hn] at h ⊢
    exact hpair _ _ h
  · simp only [slotK, slotAtG, dif_neg hn] at h ⊢
    match s, a, h with
    | ⟨0, _⟩, _, _ => exact hnev u
    | ⟨1, _⟩, a, h => exact hpair _ _ h

omit [Leaf S.sig] [Shapes S] [TopLaws S] in
/-- The open block that `blockK` tests agrees: the block of a left object, against a term. -/
theorem blockK_agree {N N' : Nat} (φL : Graph S.sig N → Mean.C S.sig) (φR : Graph S.sig N' → Mean.C S.sig)
    {Rc : Graph S.sig N → Graph S.sig N' → Bool} {fs : Finset String}
    {md : {x // x ∈ fs} → SlotMode S.sig} (s : Fin 2) (a : (TOp.obj fs md s).Pos → Graph S.sig N)
    (hpair : ∀ p u, Rc (a p) u = true → Agree o (φL (a p)) (φR u)) (hs : s.val ≠ 0) (u : Graph S.sig N')
    (h : blockK (md := md) s (fun p => Rc (a p)) u = true) :
    Agree o (φL (blockG (md := md) s a)) (φR u) := by
  match s, a, h, hs with
  | ⟨0, _⟩, _, _, hs => exact absurd rfl hs
  | ⟨1, _⟩, a, h, _ => exact hpair _ _ h

omit [Leaf S.sig] [Shapes S] [TopLaws S] in
/-- **Two objects agree** where each pair of slots that `objK` tests agrees, and the two slots at
    each name answer alike at absence. -/
theorem obj_agree {N N' : Nat} (φL : Graph S.sig N → Mean.C S.sig) (φR : Graph S.sig N' → Mean.C S.sig)
    {Rc : Graph S.sig N → Graph S.sig N' → Bool} {fs fs' : Finset String}
    {md : {x // x ∈ fs} → SlotMode S.sig} {md' : {x // x ∈ fs'} → SlotMode S.sig} {s s' : Fin 2}
    (a : (TOp.obj fs md s).Pos → Graph S.sig N) (b : (TOp.obj fs' md' s').Pos → Graph S.sig N')
    (h : objK (md := md) o a (fun p => Rc (a p)) (.node (.obj fs' md' s') b) = true)
    (hpair : ∀ p u, Rc (a p) u = true → Agree o (φL (a p)) (φR u))
    (hnev : ∀ u, Agree o (φL Graph.never) (φR u)) :
    Agree o (TOp.run τ (.obj fs md s) fun p => φL (a p)) (TOp.run τ (.obj fs' md' s') fun q => φR (b q)) := by
  simp only [objK, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨H1, H2⟩, H3⟩ := h
  simp only [TOp.run]
  split
  · next F _ =>
    refine agree_object (fun n c₁ c₂ h1 h2 => ?_) (fun n y₁ y₂ e1 e2 => ?_)
    · obtain ⟨rfl, hb1⟩ := entry_of_slot φL a n h1
      obtain ⟨rfl, hb2⟩ := entry_of_slot φR b n h2
      rcases Decidable.em (n ∈ fs) with hn | hn
      · have := (H1 ⟨n, hn⟩ (keyPos_complete fs _)).2
        rw [slotAtG_mem a ⟨n, hn⟩]
        exact hpair _ _ this
      rcases Decidable.em (n ∈ fs') with hn' | hn'
      · have := (H2 ⟨n, hn'⟩ (keyPos_complete fs' _)).2
        rw [slotAtG_mem b ⟨n, hn'⟩]
        exact slotK_agree φL φR a hpair hnev n _ this
      · obtain ⟨e1, hs⟩ := hb1 hn
        obtain ⟨e2, _⟩ := hb2 hn'
        rw [e1, e2]
        exact blockK_agree φL φR s a hpair hs _ H3
    · rw [absentOf_slot a _ .empty n] at e1
      rw [absentOf_slot b _ .empty n] at e2
      rcases Decidable.em (n ∈ fs) with hn | hn
      · have := (H1 ⟨n, hn⟩ (keyPos_complete fs _)).1
        rw [slotAtG_mem a ⟨n, hn⟩] at e1
        exact absentAgree_sound this e1 e2
      rcases Decidable.em (n ∈ fs') with hn' | hn'
      · have := (H2 ⟨n, hn'⟩ (keyPos_complete fs' _)).1
        rw [slotAtG_mem b ⟨n, hn'⟩] at e2
        exact absentAgree_sound this e1 e2
      · have m1 : (slotAtG (md := md) a n).1 = .opt := by unfold slotAtG; rw [dif_neg hn]
        have m2 : (slotAtG (md := md') b n).1 = .opt := by unfold slotAtG; rw [dif_neg hn']
        rw [m1] at e1
        rw [m2] at e2
        exact (Option.some.inj e1).symm.trans (Option.some.inj e2)
  · exact agree_empty_left _ _

omit [Leaf S.sig] [Shapes S] [TopLaws S] in
/-- Two sets agree where their elements agree. -/
theorem set_agree {cA cB : Mean.C S.sig} (h : Agree o cA cB) :
    Agree o (TOp.run τ .set fun _ => cA) (TOp.run τ .set fun _ => cB) := by
  simp only [TOp.run]
  split
  · next L _ => exact agree_of_agreeS (fun _ h' => L.agreeS h') o h
  · exact agree_empty_left _ _

/-! ### The rows -/

/-- **An identification of entries is sound** where each pair of entries that it names has one
    meaning. -/
def IdentSound {NL NR : Nat} (cL : Closed S.sig NL) (cR : Closed S.sig NR)
    (ι : Fin NL → Fin NR → Bool) : Prop :=
  ∀ i j, ι i j = true → Closed.meaning τ cL i = Closed.meaning τ cR j

omit [Leaf S.sig] [Shapes S] [TopLaws S] in
/-- Two scopes identify no entry, so their identification is sound. -/
theorem identSound_twoScopes {NL NR : Nat} (cL : Closed S.sig NL) (cR : Closed S.sig NR) :
    IdentSound (τ := τ) cL cR twoScopes :=
  fun _ _ h => nomatch h

omit [Leaf S.sig] [Shapes S] [TopLaws S] in
/-- One scope identifies an entry with itself only, so its identification is sound. -/
theorem identSound_oneScope {N : Nat} (c : Closed S.sig N) : IdentSound (τ := τ) c c oneScope :=
  fun _ _ h => by rw [of_decide_eq_true h]

variable {cL : Closed S.sig NL} {cR : Closed S.sig NR} {ι : Fin NL → Fin NR → Bool}

/-- **A guarded left node**: each answer of a term that its rows admit is the left answer, where
    each answer of a term of the family is. -/
theorem guard_at (laws : Laws S o) {R : Graph S.sig NL → Graph S.sig NR → Prop}
    (hR : PostT (rowSpecC cL.graph cR.graph o ι) R) {op : TOp S.sig} {a : op.Pos → Graph S.sig NL}
    {v w : Mean.V (B := S.sig)} (hx : (mng τ (Closed.toG τ cL) (.node op a)).f o v = some w)
    (hfam : ∀ Rr Rc, SubR Rr R → SubR Rc R → ∀ y' b, famN o op a (fun p => Rc (a p)) y' = true →
      (mng τ (Closed.toG τ cR) y').f o v = some b → w = b)
    (heq : ∀ Rr Rc y, rowT (rowSpecC cL.graph cR.graph o ι) Rr Rc (.node op a) y =
      rightC cR.graph (Rr (.node op a)) (fun y' => cbaseG cL.graph cR.graph o (.node op a) y' ||
        famN o op a (fun p => Rc (a p)) y') y) :
    ∀ Rr Rc, SubR Rr R → SubR Rc R → ∀ y,
      rowT (rowSpecC cL.graph cR.graph o ι) Rr Rc (.node op a) y = true →
      ∀ z, (mng τ (Closed.toG τ cR) y).f o v = some z → w = z := by
  have fam' : ∀ Rr Rc, SubR Rr R → SubR Rc R → ∀ y' b,
      (cbaseG cL.graph cR.graph o (.node op a) y' || famN o op a (fun p => Rc (a p)) y') = true →
      (mng τ (Closed.toG τ cR) y').f o v = some b → w = b := by
    intro Rr Rc hr hc y' b h hb
    simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · exact cbaseG_sound laws cL cR h v w b hx hb
    · exact hfam Rr Rc hr hc y' b h hb
  intro Rr Rc hr hc y h
  rw [heq] at h
  refine rightC_mng (Closed.toG τ cR) (G := fun b => w = b) (P := R (.node op a)) (fun y' h' => ?_)
    (hr _) (fam' Rr Rc hr hc) y h
  rcases hR _ _ h' with ⟨Rr', Rc', h1, h3, h4⟩ | ⟨i, _, hxi, _⟩
  · rw [heq] at h4; exact ⟨_, _, h1 _, fam' Rr' Rc' h1 h3, h4⟩
  · exact nomatch hxi

omit [Shapes S] [TopLaws S] in
/-- **The relation from the rows**, at one input. -/
theorem rformC {R : Graph S.sig NL → Graph S.sig NR → Prop} (hR : PostT (rowSpecC cL.graph cR.graph o ι) R)
    {x : Graph S.sig NL} {v w : Mean.V (B := S.sig)}
    (hrows : ∀ Rr Rc, SubR Rr R → SubR Rc R → ∀ y,
      rowT (rowSpecC cL.graph cR.graph o ι) Rr Rc x y = true →
      ∀ z, (mng τ (Closed.toG τ cR) y).f o v = some z → w = z)
    (hleaf : ∀ i j, x = .leaf i → R (cL.graph i) (cR.graph j) →
      ∀ z, (mng τ (Closed.toG τ cR) (cR.graph j)).f o v = some z → w = z) :
    ∀ y, R x y → ∀ z, (mng τ (Closed.toG τ cR) y).f o v = some z → w = z := by
  intro y hy z hz
  rcases hR x y hy with ⟨Rr, Rc, h1, h3, h4⟩ | ⟨i, j, rfl, rfl, h⟩
  · exact hrows Rr Rc h1 h3 _ h4 z hz
  · rw [congrFun (congrFun (mng_leaf (Closed.toG τ cR) j) o) v] at hz
    exact hleaf i j rfl h z hz

/-- **Soundness of `compat` by rule induction on the left derivation**, over a relation
    post-fixed up to unfolding: where the left term answers, each term that the relation pairs
    with the left term gives the same answer. A container reads its children at a smaller depth
    of the datum, through `AgB`. A `held` reads the derivation of its inner term, which has no
    leaf, at each input. -/
theorem post_soundC (laws : Laws S o) (hι : IdentSound (τ := τ) cL cR ι)
    {R : Graph S.sig NL → Graph S.sig NR → Prop}
    (hR : PostT (rowSpecC cL.graph cR.graph o ι) R) :
    ∀ {x o' v r}, Eval (Closed.toG τ cL) x o' v r → o' = o → ∀ w, r = some w → Good x →
      (∀ Rr Rc, SubR Rr R → SubR Rc R → ∀ y,
        rowT (rowSpecC cL.graph cR.graph o ι) Rr Rc x y = true →
        ∀ z, (mng τ (Closed.toG τ cR) y).f o v = some z → w = z) ∧
      ∀ y, R x y → ∀ z, (mng τ (Closed.toG τ cR) y).f o v = some z → w = z := by
  intro x o' v r h
  induction h with
  | @leaf i o' v r h0 ih =>
    intro ho w hw _; subst o'
    have hx := (mng_of_eval _ (Eval.leaf h0)).trans hw
    have IH := ih rfl w hw (fun j => (SSys.order cL).2 i j)
    have hrows : ∀ Rr Rc, SubR Rr R → SubR Rc R → ∀ y,
        rowT (rowSpecC cL.graph cR.graph o ι) Rr Rc (.leaf i) y = true →
        ∀ z, (mng τ (Closed.toG τ cR) y).f o v = some z → w = z := by
      intro Rr Rc hr _ y h z hz
      simp only [rowT, rowSpecC, Bool.or_eq_true] at h
      rcases h with (h | h) | h
      · exact cbaseG_sound laws cL cR h v w z hx hz
      · cases y with
        | leaf j =>
          have hz' : (Closed.meaning τ cR j).f o v = some z := hz
          rw [← hι i j h] at hz'
          exact Option.some.inj (hx.symm.trans hz')
        | node _ _ => exact nomatch h
      · exact IH.2 y (hr _ _ h) z hz
    exact ⟨hrows, rformC hR hrows fun i' j hxi h => by cases hxi; exact IH.2 _ h⟩
  | @prim g a o' v =>
    intro ho w hw _; subst o'
    have hrows := guard_at (τ := τ) (op := .prim g) (a := a) laws hR
      ((mng_of_eval _ Eval.prim).trans hw)
      (fun _ _ _ _ _ _ h _ => nomatch h) (fun _ _ _ => rfl)
    exact ⟨hrows, rformC hR hrows fun _ _ h => nomatch h⟩
  | @opaq a o' v =>
    intro ho w hw _; subst o'
    have hrows := guard_at (τ := τ) (op := .opaq) (a := a) laws hR
      ((mng_of_eval _ Eval.opaq).trans hw)
      (fun _ _ _ _ _ _ h _ => nomatch h) (fun _ _ _ => rfl)
    exact ⟨hrows, rformC hR hrows fun _ _ h => nomatch h⟩
  | never => exact fun _ w hw => nomatch hw
  | @refine p pA a o' v r h0 ih =>
    intro ho w hw hg; subst o'
    have hx := (mng_of_eval _ (Eval.refine h0)).trans hw
    have IH := ih rfl w (bind_some_eq hw) (good_child hg (fun h => nomatch h) ())
    have hrows : ∀ Rr Rc, SubR Rr R → SubR Rc R → ∀ y,
        rowT (rowSpecC cL.graph cR.graph o ι) Rr Rc (.node (.refine p pA) a) y = true →
        ∀ z, (mng τ (Closed.toG τ cR) y).f o v = some z → w = z := by
      intro Rr Rc hr hc y h z hz
      simp only [rowT, rowSpecC, Bool.or_eq_true] at h
      rcases h with h | h
      · exact cbaseG_sound laws cL cR h v w z hx hz
      · exact IH.1 Rr Rc hr hc y h z hz
    exact ⟨hrows, rformC hR hrows fun _ _ h => nomatch h⟩
  | unionNil => exact fun _ w hw => nomatch hw
  | @unionHead m o' v w' a h0 ih =>
    intro ho w hw hg; subst o'
    have hx := (mng_of_eval _ (Eval.unionHead h0)).trans hw
    have IH := ih rfl w hw (good_child hg (fun h => nomatch h) (0 : Fin (m + 1)))
    have hrows : ∀ Rr Rc, SubR Rr R → SubR Rc R → ∀ y,
        rowT (rowSpecC cL.graph cR.graph o ι) Rr Rc (.node (.union (m + 1)) a) y = true →
        ∀ z, (mng τ (Closed.toG τ cR) y).f o v = some z → w = z := by
      intro Rr Rc hr hc y h z hz
      simp only [rowT, rowSpecC, Bool.or_eq_true, List.all_eq_true, List.mem_finRange, true_implies] at h
      rcases h with h | h
      · exact cbaseG_sound laws cL cR h v w z hx hz
      · exact IH.1 Rr Rc hr hc y (h 0) z hz
    exact ⟨hrows, rformC hR hrows fun _ _ h => nomatch h⟩
  | @unionTail m o' v r a h0 h1 _ ih =>
    intro ho w hw hg; subst o'
    have hx := (mng_of_eval _ (Eval.unionTail h0 h1)).trans hw
    have IH := ih rfl w hw (good_tail hg)
    have hrows : ∀ Rr Rc, SubR Rr R → SubR Rc R → ∀ y,
        rowT (rowSpecC cL.graph cR.graph o ι) Rr Rc (.node (.union (m + 1)) a) y = true →
        ∀ z, (mng τ (Closed.toG τ cR) y).f o v = some z → w = z := by
      intro Rr Rc hr hc y h z hz
      simp only [rowT, rowSpecC, Bool.or_eq_true, List.all_eq_true, List.mem_finRange, true_implies] at h
      rcases h with h | h
      · exact cbaseG_sound laws cL cR h v w z hx hz
      · exact IH.1 Rr Rc hr hc y (by
          simp only [rowT, rowSpecC, Bool.or_eq_true, List.all_eq_true, List.mem_finRange, true_implies]
          exact Or.inr fun p => h p.succ) z hz
    exact ⟨hrows, rformC hR hrows fun _ _ h => nomatch h⟩
  | @down op a o' v hk C hC ih =>
    intro ho w hw hg; subst o'
    have hx := (mng_of_eval _ (Eval.down hk C hC)).trans hw
    have hgc : ∀ p, Good (a p) := good_child hg fun h => by rw [hk] at h; exact nomatch h
    obtain ⟨j, hj⟩ : ∃ j, Mean.d (B := S.sig) v = j + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos (Mean.d_pos (B := S.sig) v)).symm⟩
    have hAB : ∀ t, (t = Graph.never ∨ ∃ p, a p = t) → ∀ y', R t y' →
        AgB o (j + 1) (mng τ (Closed.toG τ cL) t) (mng τ (Closed.toG τ cR) y') := by
      rintro t (rfl | ⟨p, rfl⟩) y' hy' u hu y₁ z₁ h1 h2
      · exact nomatch h1
      · rw [mng_of_eval _ (hC p o u (hj ▸ hu))] at h1
        exact (ih p o u (hj ▸ hu) rfl y₁ h1 (hgc p)).2 y' hy' z₁ h2
    have hv : Mean.d (B := S.sig) v < j + 2 := by rw [hj]; exact Nat.lt_succ_self _
    cases op with
    | set =>
      have hrows := guard_at (τ := τ) laws hR hx (fun Rr Rc hr hc y' b h hb => by
        cases y' with
        | leaf _ => exact nomatch h
        | node op' b' =>
          cases op' with
          | set =>
            simp only [famN] at h
            exact AgB.down (τ := τ) rfl rfl
              (set_agree (τ := τ) (agree_trunc (hAB _ (Or.inr ⟨(), rfl⟩) _ (hc _ _ h)))) v hv w b hx hb
          | prim _ | opaq | never | held _ _ _ | list _ _ _ | refine _ _ | legacy _ | obj _ _ _
          | union _ => exact nomatch h) (fun _ _ _ => rfl)
      exact ⟨hrows, rformC hR hrows fun _ _ h => nomatch h⟩
    | list n s m =>
      have hrows := guard_at (τ := τ) laws hR hx (fun Rr Rc hr hc y' b h hb => by
        cases y' with
        | leaf _ => exact nomatch h
        | node op' b' =>
          cases op' with
          | list n' s' m' =>
            simp only [famN] at h
            refine AgB.down (τ := τ) (op := .list n s m) (op' := .list n' s' m')
              (a := fun p => mng τ (Closed.toG τ cL) (a p)) (b := fun q => mng τ (Closed.toG τ cR) (b' q))
              (j := j) rfl rfl ?_ v hv w b hx hb
            refine agree_runList (τ := τ) fun k r₁ r₂ h₁ h₂ => ?_
            rw [rowOfG_listPartsX] at h₁
            have h₂' : (rowOfG (listParts b').1 (listParts b').2.1 (listParts b').2.2 k).map
                (List.map fun t => trunc j (mng τ (Closed.toG τ cR) t)) = some r₂ := by
              rw [← rowOfG_listParts (fun t => trunc j (mng τ (Closed.toG τ cR) t)) b' k]; exact h₂
            cases hT₁ : rowOfG (listPartsX (B := S.sig) (a := n) (s := s) (b := m) fun p => p).1
                (listPartsX (B := S.sig) (a := n) (s := s) (b := m) fun p => p).2.1
                (listPartsX (B := S.sig) (a := n) (s := s) (b := m) fun p => p).2.2 k with
            | none => rw [hT₁] at h₁; exact nomatch h₁
            | some t₁ =>
              cases hT₂ : rowOfG (listParts b').1 (listParts b').2.1 (listParts b').2.2 k with
              | none => rw [hT₂] at h₂'; exact nomatch h₂'
              | some t₂ =>
                rw [hT₁] at h₁; rw [hT₂] at h₂'
                obtain rfl := (Option.some.inj h₁).symm
                obtain rfl := (Option.some.inj h₂').symm
                exact List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr
                  (alignedAll_forall₂ (fun p y hy => agree_trunc
                    (hAB _ (Or.inr ⟨p, rfl⟩) _ (hc _ _ hy))) h k _ _ hT₁ hT₂))
          | prim _ | opaq | never | held _ _ _ | set | refine _ _ | legacy _ | obj _ _ _
          | union _ => exact nomatch h) (fun _ _ _ => rfl)
      exact ⟨hrows, rformC hR hrows fun _ _ h => nomatch h⟩
    | obj fs md s =>
      have hrows := guard_at (τ := τ) laws hR hx (fun Rr Rc hr hc y' b h hb => by
        cases y' with
        | leaf _ => exact nomatch h
        | node op' b' =>
          cases op' with
          | obj fs' md' s' =>
            exact AgB.down (τ := τ) rfl rfl (obj_agree (τ := τ)
              (fun t => trunc j (mng τ (Closed.toG τ cL) t)) (fun t => trunc j (mng τ (Closed.toG τ cR) t))
              a b' h (fun p u hu => agree_trunc (hAB (a p) (Or.inr ⟨p, rfl⟩) u (hc _ _ hu)))
              (fun u => agree_trunc (fun w hw y₁ z₁ h1 _ => nomatch h1))) v hv w b hx hb
          | prim _ | opaq | never | held _ _ _ | set | refine _ _ | legacy _ | list _ _ _
          | union _ => exact nomatch h) (fun _ _ _ => rfl)
      exact ⟨hrows, rformC hR hrows fun _ _ h => nomatch h⟩
    | _ => exact nomatch hk
  | @wall op a o' v hk hC ih =>
    intro ho w hw hg; subst o'
    have hx := (mng_of_eval _ (Eval.wall hk hC)).trans hw
    cases op with
    | held s k₀ ks =>
      have hnl := noLeaf_wall hg rfl true
      have hin : ∀ y', R (a true) y' →
          Agree o (mng τ (Closed.toG τ cL) (a true)) (mng τ (Closed.toG τ cR) y') :=
        fun y' hy' u y₁ z₁ h1 h2 => (ih true hnl o u rfl y₁ h1 (good_of_noLeaf hnl)).2 y' hy' z₁ h2
      have hrows := guard_at (τ := τ) laws hR hx (fun Rr Rc hr hc y' b h hb => by
        cases y' with
        | leaf _ => exact nomatch h
        | node op' b' =>
          cases op' with
          | held s' k₀' ks' =>
            simp only [famN, Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨he, hs'⟩ := h
            cases he
            exact agree_of_agreeS (fun _ h' => agreeS_held1 h') o (hin (b' true) (hc _ _ hs'))
              v w b hx hb
          | prim _ | opaq | never | set | list _ _ _ | refine _ _ | legacy _ | obj _ _ _ | union _ =>
            exact nomatch h) (fun _ _ _ => rfl)
      exact ⟨hrows, rformC hR hrows fun _ _ h => nomatch h⟩
    | legacy _ =>
      have hrows := guard_at (τ := τ) laws hR hx
        (fun _ _ _ _ _ _ h _ => nomatch h) (fun _ _ _ => rfl)
      exact ⟨hrows, rformC hR hrows fun _ _ h => nomatch h⟩
    | _ => exact nomatch hk

end Sound

/-- **Soundness of one half**: where `compat` answers `true`, the two meanings agree at the
    orientation. -/
theorem compat_sound {S : Syn} [Sem S] [Leaf S.sig] [Shapes S] [TopLaws S]
    {τ : (s : Bool) → TableAt S.sig s} {o : Orient} (laws : Laws S o) {NL NR : Nat}
    {dL : Closed S.sig NL} {dR : Closed S.sig NR} {rL : Fin NL} {rR : Fin NR}
    {ι : Fin NL → Fin NR → Bool} (hι : IdentSound (τ := τ) dL dR ι)
    (h : compat o ι dL rL dR rR = true) :
    Agree o (Closed.meaning τ dL rL) (Closed.meaning τ dR rR) := by
  intro v w z hw hz
  have he := eval_of_mng (Closed.toG τ dL) (.leaf rL) o v
  rw [show (mng τ (Closed.toG τ dL) (.leaf rL)).f o v = some w from hw] at he
  exact (post_soundC (cL := dL) (cR := dR) laws hι (vis_postW (rowSpecC dL.graph dR.graph o ι)) he rfl w rfl
    (fun _ => rfl)).2 _ (vis_root dL.graph dR.graph _ h) z hz

/-- **Soundness of the pair**: where `compatPair` answers `true`, the two meanings agree at the
    host and at the dual. -/
theorem compatPair_sound {S : Syn} [Sem S] [Leaf S.sig] [Shapes S] [TopLaws S]
    {τ : (s : Bool) → TableAt S.sig s} (laws : ∀ o, Laws S o) {NL NR : Nat}
    {dL : Closed S.sig NL} {dR : Closed S.sig NR} {rL : Fin NL} {rR : Fin NR}
    {ι : Fin NL → Fin NR → Bool} (hι : IdentSound (τ := τ) dL dR ι)
    (h : compatPair ι dL rL dR rR = true) :
    Agree .host (Closed.meaning τ dL rL) (Closed.meaning τ dR rR) ∧
      Agree .dual (Closed.meaning τ dL rL) (Closed.meaning τ dR rR) := by
  simp only [compatPair, Bool.and_eq_true] at h
  exact ⟨compat_sound (laws .host) hι h.1, compat_sound (laws .dual) hι h.2⟩

end Calculus.Alg.Scoped
