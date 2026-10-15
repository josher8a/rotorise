import Calculus.Lang.ScopeDisjoint

/-!
# Compatibility over the graph of a closed codec

`Scoped.compat` decides one half of the compatibility of two closed codecs: at the orientation, two
maps that answer at one input give one output. The decision reads the flat graph of each closed
codec, with one row per operation of the left operand. Each row is one of two warrants: the two
terms share no datum there, or both lie below the top. Below a guard, the decision assumes a pair
of entries while it compares the two bodies. A fuel bounds the walk, and an empty fuel answers
`false`.

`Scoped.compat_sound` states the soundness against `Closed.meaning`. The pairs that the walk visits
form one relation (`Vis`), and the relation is post-fixed up to the unfolding of two entries
(`vis_postC`). The proof is a rule induction on the derivation of the left answer (`Eval`), with
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

variable {sL sR}

/-- **Two objects agree** where the two slots at each declared name agree and answer alike at
    absence, and where the two open blocks agree. -/
def objC (prev : Tbl NL NR → Graph B NL → Graph B NR → Bool) (A : Tbl NL NR)
    {fs : Finset String} {md : {x // x ∈ fs} → SlotMode B} {s : Fin 2}
    (a : (TOp.obj fs md s).Pos → Graph B NL) : Graph B NR → Bool
  | .node (.obj fs' md' s') b =>
      (keyPos fs).all (fun x => (!o.c || absentAgreeG (md x) (slotAtG (md := md') b x.1).1) &&
        pairAt (sL := sL) (sR := sR) prev A (a (.inl x)) (slotAtG (md := md') b x.1).2) &&
      (keyPos fs').all (fun x => (!o.c || absentAgreeG (slotAtG (md := md) a x.1).1 (md' x)) &&
        pairAt (sL := sL) (sR := sR) prev A (slotAtG (md := md) a x.1).2 (b (.inl x))) &&
      (s.val == 0 || pairAt (sL := sL) (sR := sR) prev A (blockG (md := md) s a) (blockG (md := md') s' b))
  | _ => false

variable (sL sR)

/-- **One row per operation of the left operand**, with `prev` as the walk at the next fuel. -/
def rowC (prev : Tbl NL NR → Graph B NL → Graph B NR → Bool) (A : Tbl NL NR) :
    Graph B NL → Graph B NR → Bool
  | .leaf j, y => cbaseG sL sR o (.leaf j) y || prev A (sL j) y
  | .node .never _, _ => true
  | .node (.refine q qA) a, y => cbaseG sL sR o (.node (.refine q qA) a) y || rowC prev A (a ()) y
  | .node (.union m) a, y => cbaseG sL sR o (.node (.union m) a) y ||
      (List.finRange m).all fun p => rowC prev A (a p) y
  | .node (.held s k₀ ks) a, y => rightC sR (prev A (.node (.held s k₀ ks) a))
      (fun y' => cbaseG sL sR o (.node (.held s k₀ ks) a) y' || match y' with
        | .node (.held s' k₀' ks') b =>
            decide ((⟨s, k₀ :: ks⟩ : (s : Bool) × List (B.G s × Bool)) = ⟨s', k₀' :: ks'⟩) &&
              rowC prev [] (a true) (b true)
        | _ => false) y
  | .node .set a, y => rightC sR (prev A (.node .set a))
      (fun y' => cbaseG sL sR o (.node .set a) y' || match y' with
        | .node .set b => rowC prev [] (a ()) (b ())
        | _ => false) y
  | .node (.list n s m) a, y => rightC sR (prev A (.node (.list n s m) a))
      (fun y' => cbaseG sL sR o (.node (.list n s m) a) y' || match y' with
        | .node (.list n' s' m') b => (TOp.pos (B := B) (.list n s m)).all fun p =>
            (TOp.pos (B := B) (.list n' s' m')).all fun q => pairAt (sL := sL) (sR := sR) prev A (a p) (b q)
        | _ => false) y
  | .node (.obj fs md s) a, y => rightC sR (prev A (.node (.obj fs md s) a))
      (fun y' => cbaseG sL sR o (.node (.obj fs md s) a) y' ||
        objC (sL := sL) (sR := sR) (md := md) o prev A a y') y
  | .node (.prim g) a, y => rightC sR (prev A (.node (.prim g) a)) (cbaseG sL sR o (.node (.prim g) a)) y
  | .node .opaq a, y => rightC sR (prev A (.node .opaq a)) (cbaseG sL sR o (.node .opaq a)) y
  | .node (.legacy r) a, y =>
      rightC sR (prev A (.node (.legacy r) a)) (cbaseG sL sR o (.node (.legacy r) a)) y

/-- **The walk at a fuel.** Each unfolding of an entry and each pair below a guard spends one. -/
def compG : Nat → Tbl NL NR → Graph B NL → Graph B NR → Bool
  | 0 => fun _ _ _ => false
  | n + 1 => rowC sL sR o (compG n)

/-- `objC` with the child below a guard as one test. -/
def objC3 (Rc : Graph B NL → Graph B NR → Bool) {fs : Finset String} {md : {x // x ∈ fs} → SlotMode B}
    {s : Fin 2} (a : (TOp.obj fs md s).Pos → Graph B NL) : Graph B NR → Bool
  | .node (.obj fs' md' s') b =>
      (keyPos fs).all (fun x => (!o.c || absentAgreeG (md x) (slotAtG (md := md') b x.1).1) &&
        Rc (a (.inl x)) (slotAtG (md := md') b x.1).2) &&
      (keyPos fs').all (fun x => (!o.c || absentAgreeG (slotAtG (md := md) a x.1).1 (md' x)) &&
        Rc (slotAtG (md := md) a x.1).2 (b (.inl x))) &&
      (s.val == 0 || Rc (blockG (md := md) s a) (blockG (md := md') s' b))
  | _ => false

/-- The family of a guarded left node beside a node of its class: the set element and the inner
    term of a `held` at the test `Rs`, and each child of a list or an object at the test `Rc`. -/
def famC (Rs Rc : Graph B NL → Graph B NR → Bool) : Graph B NL → Graph B NR → Bool
  | .node (.held s k₀ ks) a, .node (.held s' k₀' ks') b =>
      decide ((⟨s, k₀ :: ks⟩ : (s : Bool) × List (B.G s × Bool)) = ⟨s', k₀' :: ks'⟩) && Rs (a true) (b true)
  | .node .set a, .node .set b => Rs (a ()) (b ())
  | .node (.list n s m) a, .node (.list n' s' m') b => (TOp.pos (B := B) (.list n s m)).all fun p =>
      (TOp.pos (B := B) (.list n' s' m')).all fun q => Rc (a p) (b q)
  | .node (.obj _ md _) a, y => objC3 o Rc (md := md) a y
  | _, _ => false

/-- **The rows of `compat` with one test per role**: `Rr` at a restart, `Rs` at the set element and
    the inner term of a `held`, and `Rc` at a child below a guard. -/
def rowC3 (Rr Rs Rc : Graph B NL → Graph B NR → Bool) : Graph B NL → Graph B NR → Bool
  | .leaf j, y => cbaseG sL sR o (.leaf j) y || Rr (sL j) y
  | .node .never _, _ => true
  | .node (.refine q qA) a, y => cbaseG sL sR o (.node (.refine q qA) a) y || rowC3 Rr Rs Rc (a ()) y
  | .node (.union m) a, y => cbaseG sL sR o (.node (.union m) a) y ||
      (List.finRange m).all fun p => rowC3 Rr Rs Rc (a p) y
  | x, y => rightC sR (Rr x) (fun y' => cbaseG sL sR o x y' || famC o Rs Rc x y') y

end Rows

/-- **One half of the compatibility of two closed codecs**, at their roots and at the orientation.
    The fuel is the fuel of `disjoint`. -/
def compat [Mean B] [Leaf B] {NL NR : Nat} (o : Orient) (dL : Closed B NL) (rL : Fin NL)
    (dR : Closed B NR) (rR : Fin NR) : Bool :=
  compG dL.graph dR.graph o (fuel NL NR) [] (.leaf rL) (.leaf rR)

/-- **The compatibility of two closed codecs**: both halves, at the host and at the dual. -/
def compatPair [Mean B] [Leaf B] {NL NR : Nat} (dL : Closed B NL) (rL : Fin NL) (dR : Closed B NR)
    (rR : Fin NR) : Bool :=
  compat .host dL rL dR rR && compat .dual dL rL dR rR

/-! ## The pairs that the walk visits -/

section Visited
variable [Mean B] [Leaf B] {NL NR : Nat} (sL : Fin NL → Graph B NL) (sR : Fin NR → Graph B NR)
  (o : Orient)

/-- **The row of the walk is the row with three tests**: the walk at the table, the row at the
    empty table, and the pair test. -/
theorem rowC_eq (prev : Tbl NL NR → Graph B NL → Graph B NR → Bool) (A : Tbl NL NR) :
    ∀ x y, rowC sL sR o prev A x y =
      rowC3 sL sR o (prev A) (rowC sL sR o prev []) (pairAt (sL := sL) (sR := sR) prev A) x y := by
  intro x
  induction x with
  | leaf j => intro y; rfl
  | node op a ih =>
    intro y
    cases op with
    | refine _ _ => simp only [rowC, rowC3]; exact congrArg _ (ih () y)
    | union m => simp only [rowC, rowC3]; exact congrArg _ (congrArg _ (funext fun p => ih p y))
    | never => rfl
    | prim _ => exact congrArg (fun f => rightC sR (prev A _) f y) (funext fun y' => (Bool.or_false _).symm)
    | opaq => exact congrArg (fun f => rightC sR (prev A _) f y) (funext fun y' => (Bool.or_false _).symm)
    | legacy _ => exact congrArg (fun f => rightC sR (prev A _) f y) (funext fun y' => (Bool.or_false _).symm)
    | held _ _ _ =>
      simp only [rowC, rowC3]; congr 1; funext y'
      cases y' with
      | leaf _ => rfl
      | node op' b => cases op' <;> rfl
    | set =>
      simp only [rowC, rowC3]; congr 1; funext y'
      cases y' with
      | leaf _ => rfl
      | node op' b => cases op' <;> rfl
    | list _ _ _ =>
      simp only [rowC, rowC3]; congr 1; funext y'
      cases y' with
      | leaf _ => rfl
      | node op' b => cases op' <;> rfl
    | obj _ _ _ => simp only [rowC, rowC3]; rfl

/-- **Post-fixed up to the unfolding of two entries**, for the rows of `compat`. -/
def PostC (R : Graph B NL → Graph B NR → Prop) : Prop :=
  ∀ x y, R x y → (∃ Rr Rs Rc : Graph B NL → Graph B NR → Bool,
    SubR Rr R ∧ SubR Rs R ∧ SubR Rc R ∧ rowC3 sL sR o Rr Rs Rc x y = true) ∨
    ∃ i j, x = .leaf i ∧ y = .leaf j ∧ R (sL i) (sR j)

/-- **The visited relation of `compat` is post-fixed up to unfolding.** -/
theorem vis_postC : PostC sL sR o (Vis sL sR (compG sL sR o)) := by
  rintro x y ⟨S, hS, hxy⟩
  rcases hS x y hxy with ⟨m, A, h, hA⟩ | ⟨i, j, rfl, rfl, hs⟩
  · have hA' : ∀ p ∈ A, Vis sL sR (compG sL sR o) (.leaf p.1) (.leaf p.2) :=
      fun p hp => ⟨S, hS, hA p hp⟩
    cases m with
    | zero => exact nomatch h
    | succ k =>
      refine Or.inl ⟨compG sL sR o k A, rowC sL sR o (compG sL sR o k) [],
        pairAt (sL := sL) (sR := sR) (compG sL sR o k) A,
        fun a b hab => vis_walk sL sR _ hab hA', fun a b hab => vis_root sL sR _ (m := k + 1) hab,
        vis_pairAt sL sR (compG sL sR o) hA', ?_⟩
      rw [← rowC_eq]; exact h
  · exact Or.inr ⟨i, j, rfl, rfl, S, hS, hs⟩

end Visited

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

/-- **Two lists agree** where each position of one agrees with each position of the other. -/
theorem agree_runList {n m n' m' : Nat} {s s' : Fin 2}
    {a : (TOp.list n s m (B := S.sig)).Pos → Mean.C S.sig}
    {b : (TOp.list n' s' m' (B := S.sig)).Pos → Mean.C S.sig}
    (h : ∀ p q, Agree o (a p) (b q)) :
    Agree o (TOp.run τ (.list n s m) a) (TOp.run τ (.list n' s' m') b) := by
  simp only [TOp.run]
  split
  · next L _ =>
    refine agree_list fun c hc d hd => ?_
    obtain ⟨p, rfl⟩ := mem_listSlots a hc
    obtain ⟨q, rfl⟩ := mem_listSlots b hd
    exact h p q
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

/-! ### A term with no leaf below a wall -/

/-- No leaf below a wall. -/
def Good {N : Nat} (t : Graph S.sig N) : Prop := ∀ j, t.wlv (TSig S.sig) j = false

omit [Sem S] in
/-- Each child of a node that is not a wall keeps no leaf below a wall. -/
theorem good_child {N : Nat} {op : TOp S.sig} {a : op.Pos → Graph S.sig N} (h : Good (.node op a))
    (hk : TOp.kind op ≠ .wall) (p : op.Pos) : Good (a p) :=
  fun j => Bool.eq_false_iff.mpr fun h' =>
    Bool.false_ne_true ((h j).symm.trans (Flat.wlv_node.mpr (Or.inr ⟨hk, p, h'⟩)))

omit [Sem S] in
/-- Each child of a wall with no leaf below the wall has no leaf. -/
theorem noLeaf_wall {N : Nat} {op : TOp S.sig} {a : op.Pos → Graph S.sig N} (h : Good (.node op a))
    (hk : TOp.kind op = .wall) (p : op.Pos) : NoLeaf (a p) :=
  fun j => Bool.eq_false_iff.mpr fun h' =>
    Bool.false_ne_true ((h j).symm.trans (Flat.wlv_node.mpr (Or.inl ⟨hk, p, h'⟩)))

omit [Sem S] in
/-- A term with no leaf has no leaf below a wall. -/
theorem good_of_noLeaf {N : Nat} : ∀ {t : Graph S.sig N}, NoLeaf t → Good t
  | .leaf _, _ => fun _ => rfl
  | .node _ _, h => fun j => Bool.eq_false_iff.mpr fun h' => by
    rcases Flat.wlv_node.mp h' with ⟨_, p, hp⟩ | ⟨_, p, hp⟩
    · exact Bool.false_ne_true ((noLeaf_child h p j).symm.trans hp)
    · exact Bool.false_ne_true ((good_of_noLeaf (noLeaf_child h p) j).symm.trans hp)

omit [Sem S] in
/-- The tail of a union keeps no leaf below a wall. -/
theorem good_tail {N m : Nat} {a : Fin (m + 1) → Graph S.sig N} (h : Good (.node (TOp.union (m + 1)) a)) :
    Good (.node (TOp.union m) fun p : Fin m => a p.succ) :=
  fun j => Bool.eq_false_iff.mpr fun h' => by
    rcases Flat.wlv_node.mp h' with ⟨hk, _⟩ | ⟨_, p, hp⟩
    · exact nomatch hk
    · exact Bool.false_ne_true ((good_child h (fun hk => nomatch hk) p.succ j).symm.trans hp)

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
/-- **Two objects agree** where each pair of slots that `objC3` tests agrees, and the two slots
    at each name answer alike at absence. -/
theorem obj_agree {N N' : Nat} (φL : Graph S.sig N → Mean.C S.sig) (φR : Graph S.sig N' → Mean.C S.sig)
    {Rc : Graph S.sig N → Graph S.sig N' → Bool} {fs fs' : Finset String}
    {md : {x // x ∈ fs} → SlotMode S.sig} {md' : {x // x ∈ fs'} → SlotMode S.sig} {s s' : Fin 2}
    (a : (TOp.obj fs md s).Pos → Graph S.sig N) (b : (TOp.obj fs' md' s').Pos → Graph S.sig N')
    (h : objC3 o Rc (md := md) a (.node (.obj fs' md' s') b) = true)
    (hpair : ∀ t u, Rc t u = true → (t = Graph.never ∨ ∃ p, a p = t) → Agree o (φL t) (φR u)) :
    Agree o (TOp.run τ (.obj fs md s) fun p => φL (a p)) (TOp.run τ (.obj fs' md' s') fun q => φR (b q)) := by
  simp only [objC3, Bool.and_eq_true, List.all_eq_true] at h
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
        exact hpair _ _ this (Or.inr ⟨_, rfl⟩)
      rcases Decidable.em (n ∈ fs') with hn' | hn'
      · have := (H2 ⟨n, hn'⟩ (keyPos_complete fs' _)).2
        rw [slotAtG_mem b ⟨n, hn'⟩]
        exact hpair _ _ this (slot_mem a n)
      · obtain ⟨e1, hs⟩ := hb1 hn
        obtain ⟨e2, _⟩ := hb2 hn'
        rw [e1, e2]
        have : (s.val == 0) = false := by simpa using hs
        rw [this, Bool.false_or] at H3
        exact hpair _ _ H3 (block_mem s a)
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

variable {cL : Closed S.sig NL} {cR : Closed S.sig NR}

/-- **A guarded left node**: each answer of a term that its rows admit is the left answer, where
    each answer of a term of the family is. -/
theorem guard_at (laws : Laws S o) {R : Graph S.sig NL → Graph S.sig NR → Prop}
    (hR : PostC cL.graph cR.graph o R) {x : Graph S.sig NL} {v w : Mean.V (B := S.sig)}
    (hx : (mng τ (Closed.toG τ cL) x).f o v = some w) (hnl : ∀ i, x ≠ .leaf i)
    (hfam : ∀ Rs Rc, SubR Rs R → SubR Rc R → ∀ y' b, famC o Rs Rc x y' = true →
      (mng τ (Closed.toG τ cR) y').f o v = some b → w = b)
    (heq : ∀ Rr Rs Rc y, rowC3 cL.graph cR.graph o Rr Rs Rc x y =
      rightC cR.graph (Rr x) (fun y' => cbaseG cL.graph cR.graph o x y' || famC o Rs Rc x y') y) :
    ∀ Rr Rs Rc, SubR Rr R → SubR Rs R → SubR Rc R → ∀ y, rowC3 cL.graph cR.graph o Rr Rs Rc x y = true →
      ∀ z, (mng τ (Closed.toG τ cR) y).f o v = some z → w = z := by
  have fam' : ∀ Rs Rc, SubR Rs R → SubR Rc R → ∀ y' b,
      (cbaseG cL.graph cR.graph o x y' || famC o Rs Rc x y') = true →
      (mng τ (Closed.toG τ cR) y').f o v = some b → w = b := by
    intro Rs Rc hs hc y' b h hb
    simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · exact cbaseG_sound laws cL cR h v w b hx hb
    · exact hfam Rs Rc hs hc y' b h hb
  intro Rr Rs Rc hr hs hc y h
  rw [heq] at h
  refine rightC_mng (Closed.toG τ cR) (G := fun b => w = b) (P := R x) (fun y' h' => ?_) (hr _)
    (fam' Rs Rc hs hc) y h
  rcases hR _ _ h' with ⟨Rr', Rs', Rc', h1, h2, h3, h4⟩ | ⟨i, _, hxi, _⟩
  · rw [heq] at h4; exact ⟨_, _, h1 _, fam' Rs' Rc' h2 h3, h4⟩
  · exact absurd hxi (hnl i)

omit [Shapes S] [TopLaws S] in
/-- **The relation from the rows**, at one input. -/
theorem rformC {R : Graph S.sig NL → Graph S.sig NR → Prop} (hR : PostC cL.graph cR.graph o R)
    {x : Graph S.sig NL} {v w : Mean.V (B := S.sig)}
    (hrows : ∀ Rr Rs Rc, SubR Rr R → SubR Rs R → SubR Rc R → ∀ y,
      rowC3 cL.graph cR.graph o Rr Rs Rc x y = true →
      ∀ z, (mng τ (Closed.toG τ cR) y).f o v = some z → w = z)
    (hleaf : ∀ i j, x = .leaf i → R (cL.graph i) (cR.graph j) →
      ∀ z, (mng τ (Closed.toG τ cR) (cR.graph j)).f o v = some z → w = z) :
    ∀ y, R x y → ∀ z, (mng τ (Closed.toG τ cR) y).f o v = some z → w = z := by
  intro y hy z hz
  rcases hR x y hy with ⟨Rr, Rs, Rc, h1, h2, h3, h4⟩ | ⟨i, j, rfl, rfl, h⟩
  · exact hrows Rr Rs Rc h1 h2 h3 _ h4 z hz
  · rw [congrFun (congrFun (mng_leaf (Closed.toG τ cR) j) o) v] at hz
    exact hleaf i j rfl h z hz

/-- **Soundness of `compat` by rule induction on the left derivation**, over a relation
    post-fixed up to unfolding: where the left term answers, each term that the relation pairs
    with the left term gives the same answer. A container reads its children at a smaller depth
    of the datum, through `AgB`. A `held` reads the derivation of its inner term, which has no
    leaf, at each input. -/
theorem post_soundC (laws : Laws S o) {R : Graph S.sig NL → Graph S.sig NR → Prop}
    (hR : PostC cL.graph cR.graph o R) :
    ∀ {x o' v r}, Eval (Closed.toG τ cL) x o' v r → o' = o → ∀ w, r = some w → Good x →
      (∀ Rr Rs Rc, SubR Rr R → SubR Rs R → SubR Rc R → ∀ y,
        rowC3 cL.graph cR.graph o Rr Rs Rc x y = true →
        ∀ z, (mng τ (Closed.toG τ cR) y).f o v = some z → w = z) ∧
      ∀ y, R x y → ∀ z, (mng τ (Closed.toG τ cR) y).f o v = some z → w = z := by
  intro x o' v r h
  induction h with
  | @leaf i o' v r h0 ih =>
    intro ho w hw _; subst o'
    have hx := (mng_of_eval _ (Eval.leaf h0)).trans hw
    have IH := ih rfl w hw (fun j => (SSys.order cL).2 i j)
    have hrows : ∀ Rr Rs Rc, SubR Rr R → SubR Rs R → SubR Rc R → ∀ y,
        rowC3 cL.graph cR.graph o Rr Rs Rc (.leaf i) y = true →
        ∀ z, (mng τ (Closed.toG τ cR) y).f o v = some z → w = z := by
      intro Rr Rs Rc hr _ _ y h z hz
      simp only [rowC3, Bool.or_eq_true] at h
      rcases h with h | h
      · exact cbaseG_sound laws cL cR h v w z hx hz
      · exact IH.2 y (hr _ _ h) z hz
    exact ⟨hrows, rformC hR hrows fun i' j hxi h => by cases hxi; exact IH.2 _ h⟩
  | @prim g a o' v =>
    intro ho w hw _; subst o'
    have hrows := guard_at (τ := τ) (x := .node (.prim g) a) laws hR
      ((mng_of_eval _ Eval.prim).trans hw) (fun _ h => nomatch h)
      (fun _ _ _ _ _ _ h _ => nomatch h) (fun _ _ _ _ => rfl)
    exact ⟨hrows, rformC hR hrows fun _ _ h => nomatch h⟩
  | @opaq a o' v =>
    intro ho w hw _; subst o'
    have hrows := guard_at (τ := τ) (x := .node .opaq a) laws hR
      ((mng_of_eval _ Eval.opaq).trans hw) (fun _ h => nomatch h)
      (fun _ _ _ _ _ _ h _ => nomatch h) (fun _ _ _ _ => rfl)
    exact ⟨hrows, rformC hR hrows fun _ _ h => nomatch h⟩
  | never => exact fun _ w hw => nomatch hw
  | @refine p pA a o' v r h0 ih =>
    intro ho w hw hg; subst o'
    have hx := (mng_of_eval _ (Eval.refine h0)).trans hw
    have IH := ih rfl w (bind_some_eq hw) (good_child hg (fun h => nomatch h) ())
    have hrows : ∀ Rr Rs Rc, SubR Rr R → SubR Rs R → SubR Rc R → ∀ y,
        rowC3 cL.graph cR.graph o Rr Rs Rc (.node (.refine p pA) a) y = true →
        ∀ z, (mng τ (Closed.toG τ cR) y).f o v = some z → w = z := by
      intro Rr Rs Rc hr hs hc y h z hz
      simp only [rowC3, Bool.or_eq_true] at h
      rcases h with h | h
      · exact cbaseG_sound laws cL cR h v w z hx hz
      · exact IH.1 Rr Rs Rc hr hs hc y h z hz
    exact ⟨hrows, rformC hR hrows fun _ _ h => nomatch h⟩
  | unionNil => exact fun _ w hw => nomatch hw
  | @unionHead m o' v w' a h0 ih =>
    intro ho w hw hg; subst o'
    have hx := (mng_of_eval _ (Eval.unionHead h0)).trans hw
    have IH := ih rfl w hw (good_child hg (fun h => nomatch h) (0 : Fin (m + 1)))
    have hrows : ∀ Rr Rs Rc, SubR Rr R → SubR Rs R → SubR Rc R → ∀ y,
        rowC3 cL.graph cR.graph o Rr Rs Rc (.node (.union (m + 1)) a) y = true →
        ∀ z, (mng τ (Closed.toG τ cR) y).f o v = some z → w = z := by
      intro Rr Rs Rc hr hs hc y h z hz
      simp only [rowC3, Bool.or_eq_true, List.all_eq_true, List.mem_finRange, true_implies] at h
      rcases h with h | h
      · exact cbaseG_sound laws cL cR h v w z hx hz
      · exact IH.1 Rr Rs Rc hr hs hc y (h 0) z hz
    exact ⟨hrows, rformC hR hrows fun _ _ h => nomatch h⟩
  | @unionTail m o' v r a h0 h1 _ ih =>
    intro ho w hw hg; subst o'
    have hx := (mng_of_eval _ (Eval.unionTail h0 h1)).trans hw
    have IH := ih rfl w hw (good_tail hg)
    have hrows : ∀ Rr Rs Rc, SubR Rr R → SubR Rs R → SubR Rc R → ∀ y,
        rowC3 cL.graph cR.graph o Rr Rs Rc (.node (.union (m + 1)) a) y = true →
        ∀ z, (mng τ (Closed.toG τ cR) y).f o v = some z → w = z := by
      intro Rr Rs Rc hr hs hc y h z hz
      simp only [rowC3, Bool.or_eq_true, List.all_eq_true, List.mem_finRange, true_implies] at h
      rcases h with h | h
      · exact cbaseG_sound laws cL cR h v w z hx hz
      · exact IH.1 Rr Rs Rc hr hs hc y (by
          simp only [rowC3, Bool.or_eq_true, List.all_eq_true, List.mem_finRange, true_implies]
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
      have hrows := guard_at (τ := τ) laws hR hx (fun _ h => nomatch h) (fun Rs Rc hs hc y' b h hb => by
        cases y' with
        | leaf _ => exact nomatch h
        | node op' b' =>
          cases op' with
          | set =>
            simp only [famC] at h
            exact AgB.down (τ := τ) rfl rfl
              (set_agree (τ := τ) (agree_trunc (hAB _ (Or.inr ⟨(), rfl⟩) _ (hs _ _ h)))) v hv w b hx hb
          | prim _ | opaq | never | held _ _ _ | list _ _ _ | refine _ _ | legacy _ | obj _ _ _
          | union _ => exact nomatch h) (fun _ _ _ _ => rfl)
      exact ⟨hrows, rformC hR hrows fun _ _ h => nomatch h⟩
    | list n s m =>
      have hrows := guard_at (τ := τ) laws hR hx (fun _ h => nomatch h) (fun Rs Rc hs hc y' b h hb => by
        cases y' with
        | leaf _ => exact nomatch h
        | node op' b' =>
          cases op' with
          | list n' s' m' =>
            simp only [famC, List.all_eq_true] at h
            exact AgB.down (τ := τ) rfl rfl (agree_runList (τ := τ) fun p q => agree_trunc
              (hAB _ (Or.inr ⟨p, rfl⟩) _ (hc _ _ (h p (TOp.pos_complete (B := S.sig) (.list n s m) p) q
                (TOp.pos_complete (B := S.sig) (.list n' s' m') q))))) v hv w b hx hb
          | prim _ | opaq | never | held _ _ _ | set | refine _ _ | legacy _ | obj _ _ _
          | union _ => exact nomatch h) (fun _ _ _ _ => rfl)
      exact ⟨hrows, rformC hR hrows fun _ _ h => nomatch h⟩
    | obj fs md s =>
      have hrows := guard_at (τ := τ) laws hR hx (fun _ h => nomatch h) (fun Rs Rc hs hc y' b h hb => by
        cases y' with
        | leaf _ => exact nomatch h
        | node op' b' =>
          cases op' with
          | obj fs' md' s' =>
            exact AgB.down (τ := τ) rfl rfl (obj_agree (τ := τ)
              (fun t => trunc j (mng τ (Closed.toG τ cL) t)) (fun t => trunc j (mng τ (Closed.toG τ cR) t))
              a b' h fun t u htu hm => agree_trunc (hAB t hm u (hc _ _ htu))) v hv w b hx hb
          | prim _ | opaq | never | held _ _ _ | set | refine _ _ | legacy _ | list _ _ _
          | union _ => exact nomatch h) (fun _ _ _ _ => rfl)
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
      have hrows := guard_at (τ := τ) laws hR hx (fun _ h => nomatch h) (fun Rs Rc hs hc y' b h hb => by
        cases y' with
        | leaf _ => exact nomatch h
        | node op' b' =>
          cases op' with
          | held s' k₀' ks' =>
            simp only [famC, Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨he, hs'⟩ := h
            cases he
            exact agree_of_agreeS (fun _ h' => agreeS_held1 h') o (hin (b' true) (hs _ _ hs'))
              v w b hx hb
          | prim _ | opaq | never | set | list _ _ _ | refine _ _ | legacy _ | obj _ _ _ | union _ =>
            exact nomatch h) (fun _ _ _ _ => rfl)
      exact ⟨hrows, rformC hR hrows fun _ _ h => nomatch h⟩
    | legacy _ =>
      have hrows := guard_at (τ := τ) laws hR hx (fun _ h => nomatch h)
        (fun _ _ _ _ _ _ h _ => nomatch h) (fun _ _ _ _ => rfl)
      exact ⟨hrows, rformC hR hrows fun _ _ h => nomatch h⟩
    | _ => exact nomatch hk

end Sound

/-- **Soundness of one half**: where `compat` answers `true`, the two meanings agree at the
    orientation. -/
theorem compat_sound {S : Syn} [Sem S] [Leaf S.sig] [Shapes S] [TopLaws S]
    {τ : (s : Bool) → TableAt S.sig s} {o : Orient} (laws : Laws S o) {NL NR : Nat}
    {dL : Closed S.sig NL} {dR : Closed S.sig NR} {rL : Fin NL} {rR : Fin NR}
    (h : compat o dL rL dR rR = true) :
    Agree o (Closed.meaning τ dL rL) (Closed.meaning τ dR rR) := by
  intro v w z hw hz
  have he := eval_of_mng (Closed.toG τ dL) (.leaf rL) o v
  rw [show (mng τ (Closed.toG τ dL) (.leaf rL)).f o v = some w from hw] at he
  exact (post_soundC (cL := dL) (cR := dR) laws (vis_postC dL.graph dR.graph o) he rfl w rfl
    (fun _ => rfl)).2 _ (vis_root dL.graph dR.graph _ h) z hz

/-- **Soundness of the pair**: where `compatPair` answers `true`, the two meanings agree at the
    host and at the dual. -/
theorem compatPair_sound {S : Syn} [Sem S] [Leaf S.sig] [Shapes S] [TopLaws S]
    {τ : (s : Bool) → TableAt S.sig s} (laws : ∀ o, Laws S o) {NL NR : Nat}
    {dL : Closed S.sig NL} {dR : Closed S.sig NR} {rL : Fin NL} {rR : Fin NR}
    (h : compatPair dL rL dR rR = true) :
    Agree .host (Closed.meaning τ dL rL) (Closed.meaning τ dR rR) ∧
      Agree .dual (Closed.meaning τ dL rL) (Closed.meaning τ dR rR) := by
  simp only [compatPair, Bool.and_eq_true] at h
  exact ⟨compat_sound (laws .host) h.1, compat_sound (laws .dual) h.2⟩

end Calculus.Alg.Scoped
