import Calculus.Lang.ScopeDisjoint

/-!
# Compatibility over the graph of a closed codec

`Scoped.compat` decides one half of the compatibility of two closed codecs: at the orientation, two
maps that answer at one input give one output. The decision reads the flat graph of each DAG of
scopes, with one row per operation of the left operand. Each row is one of two warrants: the two
terms share no datum there, or both lie below the top. Below a guard, the decision assumes a pair
of entries while it compares the two bodies. A fuel bounds the walk, and an empty fuel answers
`false`.

`Scoped.compat_sound` states the soundness against `Closed.meaning`. The proof is an induction on
the fuel, and at each pair below a guard an induction on the depth of the input: the decision
assumes a pair only at a smaller depth. A container reads its positions one layer down, so the
proof cuts each position at the depth (`trunc`) and reads the container through the law of the
step. A set and a `held` compare their positions with no assumed pair, so the walk below them gives
agreement at every depth. The rows that read no structure call the walk of `Scoped.disjoint`, on
the terms and on their views.
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
    decG sL sR ((NL * NR + 1) * (NL + NR + 2)) [] x y ||
    decG sL sR ((NL * NR + 1) * (NL + NR + 2)) [] (heldIn o x) (heldIn o y) ||
    decG (viewSys sL o) (viewSys sR o) ((NL * NR + 1) * (NL + NR + 2)) [] (viewG sL o x)
      (viewG sR o y)

/-- **The rows of the right operand.** `fam` answers each term first. The bottom agrees with every
    term. A union agrees where each option does, and a refinement where its inner term does. An
    entry unfolds through `restart`. -/
def rightC (restart fam : Graph B NR → Bool) : Graph B NR → Bool
  | .leaf j => fam (.leaf j) || restart (sR j)
  | .node .never _ => true
  | .node (.refine q qA) a => fam (.node (.refine q qA) a) || rightC restart fam (a ())
  | .node (.union m) a => fam (.node (.union m) a) ||
      (List.finRange m).all fun p => rightC restart fam (a p)
  | y => fam y

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

end Rows

/-- **One half of the compatibility of two closed codecs**, at their roots and at the orientation.
    The fuel is the fuel of `disjoint`. -/
def compat [Mean B] [Leaf B] {NL NR : Nat} (o : Orient) (dL : Closed B NL) (rL : Fin NL)
    (dR : Closed B NR) (rR : Fin NR) : Bool :=
  compG dL.graph dR.graph o ((NL * NR + 1) * (NL + NR + 2)) [] (.leaf rL) (.leaf rR)

/-- **The compatibility of two closed codecs**: both halves, at the host and at the dual. -/
def compatPair [Mean B] [Leaf B] {NL NR : Nat} (dL : Closed B NL) (rL : Fin NL) (dR : Closed B NR)
    (rR : Fin NR) : Bool :=
  compat .host dL rL dR rR && compat .dual dL rL dR rR

/-! ## Soundness -/

section Sound
variable {S : Syn} [Sem S] {τ : (s : Bool) → TableAt S.sig s} {o : Orient}

variable (o) in
/-- **Agreement below a depth**: two maps at the orientation that answer at one input of a smaller
    depth give one output. -/
def AgB (k : Nat) (c c' : Mean.C S.sig) : Prop :=
  ∀ x, Mean.d (B := S.sig) x < k → ∀ y z, c.f o x = some y → c'.f o x = some z → y = z

/-- Agreement gives agreement below each depth. -/
theorem AgB.of_agree {k : Nat} {c c' : Mean.C S.sig} (h : Agree o c c') : AgB o k c c' :=
  fun x _ => h x

/-- **Agreement below every depth is agreement**, because every input has a depth. -/
theorem agree_of_AgB {c c' : Mean.C S.sig} (h : ∀ k, AgB o (k + 1) c c') : Agree o c c' :=
  fun x => h (Mean.d (B := S.sig) x) x (Nat.lt_succ_self _)

/-- Any two codecs agree below the depth one, because every input has a depth of at least one. -/
theorem AgB.one (c c' : Mean.C S.sig) : AgB o 1 c c' :=
  fun x hx => absurd hx (Nat.not_lt.mpr (Mean.d_pos x))

/-- Agreement below a depth holds below each smaller depth. -/
theorem AgB.mono {k k' : Nat} {c c' : Mean.C S.sig} (hk : k' ≤ k) (h : AgB o k c c') :
    AgB o k' c c' := fun x hx => h x (by omega)

/-- Agreement below a depth reads the two codecs through their maps only. -/
theorem AgB.congr {k : Nat} {c c' c₁ c₁' : Mean.C S.sig} (h₁ : c.f = c₁.f) (h₂ : c'.f = c₁'.f)
    (h : AgB o k c c') : AgB o k c₁ c₁' := fun x hx y z hy hz => by
  rw [← h₁] at hy; rw [← h₂] at hz; exact h x hx y z hy hz

variable (o) in
/-- Agreement below a depth is a step-indexed relation. -/
def AgB.rel : StepRel S := ⟨AgB o, fun _ _ _ hx => absurd hx (Nat.not_lt_zero _), AgB.mono, AgB.congr⟩

/-- Agreement below a depth is antitone on the left. -/
theorem AgB.sub_left {k : Nat} {c c₁ X : Mean.C S.sig} (hs : Sub c c₁) (h : AgB o k c₁ X) :
    AgB o k c X := fun x hx y z hy hz => h x hx y z (hs o x y hy) hz

/-- …and on the right. -/
theorem AgB.sub_right {k : Nat} {X c c₁ : Mean.C S.sig} (hs : Sub c c₁) (h : AgB o k X c₁) :
    AgB o k X c := fun x hx y z hy hz => h x hx y z hy (hs o x z hz)

/-- A union agrees below a depth with a partner where each option does. -/
theorem AgB.alt_left {k m : Nat} {a : Fin m → Mean.C S.sig} {μ : Option (Mean.Mem (B := S.sig))}
    {X : Mean.C S.sig} (h : ∀ p, AgB o k (a p) X) : AgB o k (altCodec (List.ofFn a) μ) X :=
  fun x hx y z hy hz => by
    obtain ⟨c, hc, _, hcy⟩ := altCodec_admits hy
    obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hc
    exact h p x hx y z hcy hz

/-- …and on the right. -/
theorem AgB.alt_right {k m : Nat} {a : Fin m → Mean.C S.sig} {μ : Option (Mean.Mem (B := S.sig))}
    {X : Mean.C S.sig} (h : ∀ p, AgB o k X (a p)) : AgB o k X (altCodec (List.ofFn a) μ) :=
  fun x hx y z hy hz => by
    obtain ⟨c, hc, _, hcz⟩ := altCodec_admits hz
    obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hc
    exact h p x hx y z hy hcz

/-- Two codecs that agree below one more depth give two cut codecs that agree. -/
theorem agree_trunc {j : Nat} {c c' : Mean.C S.sig} (h : AgB o (j + 1) c c') :
    Agree o (trunc j c) (trunc j c') := fun x y z hy hz => by
  simp only [trunc] at hy hz
  split at hy
  · next hx =>
    rw [if_pos hx] at hz
    exact h x (by omega) y z hy hz
  · exact nomatch hy

/-- **A container agrees below one more depth** where its positions, cut at the depth, give two
    agreeing containers: the step reads the positions of a container one layer down. -/
theorem AgB.down {op op' : TOp S.sig} (hk : op.kind = .down) (hk' : op'.kind = .down)
    {a : op.Pos → Mean.C S.sig} {b : op'.Pos → Mean.C S.sig} {j : Nat}
    (h : Agree o (TOp.run τ op fun p => trunc j (a p)) (TOp.run τ op' fun q => trunc j (b q))) :
    AgB o (j + 2) (TOp.run τ op a) (TOp.run τ op' b) := by
  have ha := (TStep_lawful τ).down op hk j a (fun p => trunc j (a p))
    fun p => (trunc_agree j (a p)).symm
  have hb := (TStep_lawful τ).down op' hk' j b (fun q => trunc j (b q))
    fun q => (trunc_agree j (b q)).symm
  intro x hx y z hy hz
  have hx' : Mean.d (B := S.sig) x ≤ j + 1 := by omega
  have e1 : (TOp.run τ op a).f o x = (TOp.run τ op fun p => trunc j (a p)).f o x := ha.f o x hx'
  have e2 : (TOp.run τ op' b).f o x = (TOp.run τ op' fun q => trunc j (b q)).f o x := hb.f o x hx'
  rw [e1] at hy
  rw [e2] at hz
  exact h x y z hy hz

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

variable [Leaf S.sig] [Shapes S] [TopLaws S]

omit [TopLaws S] in
/-- **Two terms whose walk of `disjoint` answers `true` share no datum**, at any two positions. -/
theorem apart_of_decG (laws : Laws S o) {NL NR : Nat} (dL : GSys τ NL) (dR : GSys τ NR) {n : Nat}
    {x : Graph S.sig NL} {y : Graph S.sig NR} (h : decG dL.sys dR.sys n [] x y = true) :
    ∀ v, (((mng τ dL x).f o v).isSome && ((mng τ dR y).f o v).isSome) = false :=
  apart_of_AB fun k => decG_sound laws n [] x y h k fun _ hq => nomatch hq

/-- **Two terms whose views the walk separates share no datum**: each view admits what its term
    admits. -/
theorem apart_of_views (laws : Laws S o) {NL NR : Nat} (cL : Closed S.sig NL) (cR : Closed S.sig NR)
    {n : Nat} {x : Graph S.sig NL} {y : Graph S.sig NR}
    (h : decG (viewSys cL.graph o) (viewSys cR.graph o) n [] (viewG cL.graph o x)
      (viewG cR.graph o y) = true) :
    ∀ v, (((mng τ (Closed.toG τ cL) x).f o v).isSome &&
      ((mng τ (Closed.toG τ cR) y).f o v).isSome) = false := by
  intro v
  have hap := apart_of_decG laws (Closed.viewToG τ o cL) (Closed.viewToG τ o cR) h v
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
  · exact agree_apart (apart_of_decG laws (Closed.toG τ cL) (Closed.toG τ cR) hd)
  · exact agree_apart fun v => apart_of_imp (heldIn_dom (Closed.toG τ cL) x v)
      (apart_of_imp' (heldIn_dom (Closed.toG τ cR) y v)
        (apart_of_decG laws (Closed.toG τ cL) (Closed.toG τ cR) hh v))
  · exact agree_apart (apart_of_views laws cL cR hv)

/-! ### The walk -/

omit [Leaf S.sig] [Shapes S] [TopLaws S] in
/-- **The rows of the right operand are sound**, for a left codec that `restart` and `fam` are
    sound for. -/
theorem rightC_sound {N : Nat} (d : GSys τ N) {X : Mean.C S.sig} {k : Nat}
    {restart fam : Graph S.sig N → Bool}
    (hr : ∀ y, restart y = true → AgB o k X (mng τ d y))
    (hf : ∀ y, fam y = true → AgB o k X (mng τ d y)) :
    ∀ y, rightC d.sys restart fam y = true → AgB o k X (mng τ d y) := by
  intro y
  induction y with
  | leaf j =>
    intro h
    simp only [rightC, Bool.or_eq_true] at h
    rcases h with h | h
    · exact hf _ h
    · exact AgB.congr rfl (mng_leaf d j).symm (hr _ h)
  | node op a ih =>
    intro h
    cases op with
    | never => exact AgB.of_agree (agree_empty_right _ _)
    | refine q qA =>
      simp only [rightC, Bool.or_eq_true] at h
      rcases h with h | h
      · exact hf _ h
      · exact AgB.sub_right (sub_refine2_self _ _ _) (ih () h)
    | union m =>
      simp only [rightC, Bool.or_eq_true, List.all_eq_true, List.mem_finRange, true_implies] at h
      rcases h with h | h
      · exact hf _ h
      · exact AgB.alt_right fun p => ih p (h p)
    | prim _ => exact hf _ h
    | opaq => exact hf _ h
    | set => exact hf _ h
    | list _ _ _ => exact hf _ h
    | held _ _ _ => exact hf _ h
    | legacy _ => exact hf _ h
    | obj _ _ _ => exact hf _ h

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

/-! ### The rows -/

variable {cL : Closed S.sig NL} {cR : Closed S.sig NR}

/-- **One row per operation is sound**, for a walk at the next fuel that is sound. -/
theorem rowC_sound (laws : Laws S o)
    {prev : Tbl NL NR → Graph S.sig NL → Graph S.sig NR → Bool}
    (hp : Prev τ (AgB.rel o) (Closed.toG τ cL) (Closed.toG τ cR) prev) (x : Graph S.sig NL) :
    ∀ y A k, rowC cL.graph cR.graph o prev A x y = true →
      Hyp τ (AgB.rel o) (Closed.toG τ cL) (Closed.toG τ cR) k A →
      AgB o (k + 1) (mng τ (Closed.toG τ cL) x) (mng τ (Closed.toG τ cR) y) := by
  induction x with
  | leaf j =>
    intro y A k h hA
    simp only [rowC, Bool.or_eq_true] at h
    rcases h with h | h
    · exact AgB.of_agree (cbaseG_sound laws cL cR h)
    · exact AgB.congr (mng_leaf _ j).symm rfl (hp A _ _ h k hA)
  | node op a ih =>
    intro y A k h hA
    have base : ∀ y', cbaseG cL.graph cR.graph o (.node op a) y' = true →
        AgB o (k + 1) (mng τ (Closed.toG τ cL) (.node op a)) (mng τ (Closed.toG τ cR) y') :=
      fun y' hy' => AgB.of_agree (cbaseG_sound laws cL cR hy')
    have restart : ∀ y', prev A (.node op a) y' = true →
        AgB o (k + 1) (mng τ (Closed.toG τ cL) (.node op a)) (mng τ (Closed.toG τ cR) y') :=
      fun y' hy' => hp A _ _ hy' k hA
    cases op with
    | never =>
      intro v _ y₁ z₁ h₁ _
      exact nomatch h₁
    | refine q qA =>
      simp only [rowC, Bool.or_eq_true] at h
      rcases h with h | h
      · exact base y h
      · exact AgB.sub_left (sub_refine2_self _ _ _) (ih () y A k h hA)
    | union m =>
      simp only [rowC, Bool.or_eq_true, List.all_eq_true, List.mem_finRange, true_implies] at h
      rcases h with h | h
      · exact base y h
      · exact AgB.alt_left fun p => ih p y A k (h p) hA
    | prim g => exact rightC_sound _ restart base y h
    | opaq => exact rightC_sound _ restart base y h
    | legacy r => exact rightC_sound _ restart base y h
    | held s k₀ ks =>
      refine rightC_sound _ restart (fun y' hy' => ?_) y h
      simp only [Bool.or_eq_true] at hy'
      rcases hy' with hy' | hy'
      · exact base y' hy'
      cases y' with
      | leaf _ => exact nomatch hy'
      | node op' b =>
        cases op' with
        | held s' k₀' ks' =>
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hy'
          obtain ⟨he, hin⟩ := hy'
          cases he
          have hi : Agree o (mng τ (Closed.toG τ cL) (a true)) (mng τ (Closed.toG τ cR) (b true)) :=
            agree_of_AgB fun k' => ih true (b true) [] k' hin fun _ hq => nomatch hq
          exact AgB.of_agree (agree_of_agreeS (fun _ h' => agreeS_held1 h') o hi)
        | prim _ | opaq | never | set | list _ _ _ | refine _ _ | legacy _ | obj _ _ _ | union _ =>
          exact nomatch hy'
    | set =>
      refine rightC_sound _ restart (fun y' hy' => ?_) y h
      simp only [Bool.or_eq_true] at hy'
      rcases hy' with hy' | hy'
      · exact base y' hy'
      cases y' with
      | leaf _ => exact nomatch hy'
      | node op' b =>
        cases op' with
        | set =>
          have hi : Agree o (mng τ (Closed.toG τ cL) (a ())) (mng τ (Closed.toG τ cR) (b ())) :=
            agree_of_AgB fun k' => ih () (b ()) [] k' hy' fun _ hq => nomatch hq
          refine AgB.of_agree ?_
          show Agree o (TOp.run τ .set fun p => mng τ (Closed.toG τ cL) (a p))
            (TOp.run τ .set fun p => mng τ (Closed.toG τ cR) (b p))
          simp only [TOp.run]
          split
          · next L _ => exact agree_of_agreeS (fun _ h' => L.agreeS h') o hi
          · exact agree_empty_left _ _
        | prim _ | opaq | never | held _ _ _ | list _ _ _ | refine _ _ | legacy _ | obj _ _ _
        | union _ => exact nomatch hy'
    | list n s m =>
      refine rightC_sound _ restart (fun y' hy' => ?_) y h
      simp only [Bool.or_eq_true] at hy'
      rcases hy' with hy' | hy'
      · exact base y' hy'
      cases y' with
      | leaf _ => exact nomatch hy'
      | node op' b =>
        cases op' with
        | list n' s' m' =>
          simp only [List.all_eq_true] at hy'
          have hpq : ∀ p q, AgB o k (mng τ (Closed.toG τ cL) (a p)) (mng τ (Closed.toG τ cR) (b q)) :=
            fun p q => pairAt_soundR hp _ _ A k (hy' p (TOp.pos_complete (B := S.sig) (.list n s m) p) q
              (TOp.pos_complete (B := S.sig) (.list n' s' m') q)) hA
          cases k with
          | zero => exact AgB.one _ _
          | succ j =>
            show AgB o (j + 2) (TOp.run τ (.list n s m) fun p => mng τ (Closed.toG τ cL) (a p))
              (TOp.run τ (.list n' s' m') fun q => mng τ (Closed.toG τ cR) (b q))
            exact AgB.down rfl rfl (agree_runList fun p q => agree_trunc (hpq p q))
        | prim _ | opaq | never | held _ _ _ | set | refine _ _ | legacy _ | obj _ _ _
        | union _ => exact nomatch hy'
    | obj fs md s =>
      refine rightC_sound _ restart (fun y' hy' => ?_) y h
      simp only [Bool.or_eq_true] at hy'
      rcases hy' with hy' | hy'
      · exact base y' hy'
      cases y' with
      | leaf _ => exact nomatch hy'
      | node op' b =>
        cases op' with
        | obj fs' md' s' =>
          simp only [objC, Bool.and_eq_true, List.all_eq_true] at hy'
          obtain ⟨⟨H1, H2⟩, H3⟩ := hy'
          cases k with
          | zero => exact AgB.one _ _
          | succ j =>
            show AgB o (j + 2) (TOp.run τ (.obj fs md s) fun p => mng τ (Closed.toG τ cL) (a p))
              (TOp.run τ (.obj fs' md' s') fun q => mng τ (Closed.toG τ cR) (b q))
            refine AgB.down rfl rfl ?_
            simp only [TOp.run]
            split
            · next F _ =>
              refine agree_object (fun n c₁ c₂ h1 h2 => ?_) (fun n y₁ y₂ e1 e2 => ?_)
              · obtain ⟨rfl, hb1⟩ := entry_of_slot (fun t => trunc j (mng τ (Closed.toG τ cL) t)) a n h1
                obtain ⟨rfl, hb2⟩ := entry_of_slot (fun t => trunc j (mng τ (Closed.toG τ cR) t)) b n h2
                refine agree_trunc ?_
                rcases Decidable.em (n ∈ fs) with hn | hn
                · have := (H1 ⟨n, hn⟩ (keyPos_complete fs _)).2
                  rw [slotAtG_mem a ⟨n, hn⟩]
                  exact pairAt_soundR hp _ _ A _ this hA
                rcases Decidable.em (n ∈ fs') with hn' | hn'
                · have := (H2 ⟨n, hn'⟩ (keyPos_complete fs' _)).2
                  rw [slotAtG_mem b ⟨n, hn'⟩]
                  exact pairAt_soundR hp _ _ A _ this hA
                · obtain ⟨e1, hs⟩ := hb1 hn
                  obtain ⟨e2, _⟩ := hb2 hn'
                  rw [e1, e2]
                  have : (s.val == 0) = false := by simpa using hs
                  rw [this, Bool.false_or] at H3
                  exact pairAt_soundR hp _ _ A _ H3 hA
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
        | prim _ | opaq | never | held _ _ _ | set | refine _ _ | legacy _ | list _ _ _
        | union _ => exact nomatch hy'

/-- **The walk is sound at each fuel.** -/
theorem compG_sound (laws : Laws S o) :
    ∀ n, Prev τ (AgB.rel o) (Closed.toG τ cL) (Closed.toG τ cR) (compG cL.graph cR.graph o n)
  | 0 => fun _ _ _ h => nomatch h
  | n + 1 => fun A x y h k hA => rowC_sound laws (compG_sound laws n) x y A k h hA

end Sound

/-- **Soundness of one half**: where `compat` answers `true`, the two meanings agree at the
    orientation. -/
theorem compat_sound {S : Syn} [Sem S] [Leaf S.sig] [Shapes S] [TopLaws S]
    {τ : (s : Bool) → TableAt S.sig s} {o : Orient} (laws : Laws S o) {NL NR : Nat}
    {dL : Closed S.sig NL} {dR : Closed S.sig NR} {rL : Fin NL} {rR : Fin NR}
    (h : compat o dL rL dR rR = true) :
    Agree o (Closed.meaning τ dL rL) (Closed.meaning τ dR rR) :=
  agree_of_AgB fun k => compG_sound (cL := dL) (cR := dR) laws _ [] (.leaf rL) (.leaf rR) h k
    fun _ hq => nomatch hq

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
