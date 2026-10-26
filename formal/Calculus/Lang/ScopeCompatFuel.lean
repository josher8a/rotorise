import Calculus.Lang.ScopeCompat
import Calculus.Lang.ScopeFuel

/-!
# The fuel of agreement is adequate

`compG` answers `false` when its fuel runs out, and the optimistic walk of agreement answers `true`
there. The walk of agreement reads a pair of closed terms at the same fuel (`pairX`), so a pair of
closed terms spends no fuel, and the measure of `ScopeFuel` bounds each call. Where the optimistic
walk answers `true` at the fuel of `disjoint`, so does `compat` (`compat_of_compO`). The proof is
the generic adequacy of a row (`walkO_fuel_imp_walk`), with two hypotheses on the row of agreement:
the row keeps its answer `true` from a walk to a walk (`rowMono_C`), and the row answers `true`
against the bottom (`rowNever_C`). A `held` reads its inner terms, which hold no leaf, so the
terms of the flat system hold no leaf below a wall (`Good`), and the pair of inner terms reads no
restart (`goW_noLeaf`).
-/

namespace Calculus.Alg.Scoped

variable {B : Sig}

/-! ## The rows of two list shapes -/

/-- A position of a list node is a position of the node. -/
theorem mem_listParts {N n m : Nat} {s : Fin 2} (a : (TOp.list n s m (B := B)).Pos → Graph B N)
    {y : Graph B N}
    (h : y ∈ (listParts a).1 ∨ (listParts a).2.1 = some y ∨ y ∈ (listParts a).2.2) :
    ∃ p, a p = y := by
  rcases h with h | h | h
  · obtain ⟨p, rfl⟩ := List.mem_ofFn.mp h; exact ⟨_, rfl⟩
  · obtain ⟨p, hp⟩ := optOf_mem s _ y h; exact ⟨_, hp⟩
  · obtain ⟨p, rfl⟩ := List.mem_ofFn.mp h; exact ⟨_, rfl⟩

/-- Each right position of an aligned row is a right position of the shape. -/
theorem alignedRows_snd_mem {X Y : Type} {fpre fsuf : List X} {fsp : Option X}
    {pre₂ suf₂ : List Y} {sp₂ : Option Y} {r : List X × List Y}
    (hr : r ∈ alignedRows fpre fsp fsuf pre₂ sp₂ suf₂) :
    ∀ y ∈ r.2, y ∈ pre₂ ∨ sp₂ = some y ∨ y ∈ suf₂ := by
  intro y hy
  unfold alignedRows at hr
  cases fsp with
  | none =>
    cases h : rowOfG pre₂ sp₂ suf₂ (fpre.length + fsuf.length) with
    | none => simp [h] at hr
    | some us =>
      simp only [h, List.mem_singleton] at hr
      subst hr
      exact rowOfG_mem h y hy
  | some f =>
    cases sp₂ with
    | none =>
      cases h : rowOfG fpre (some f) fsuf (pre₂.length + suf₂.length) with
      | none => simp [h] at hr
      | some fs =>
        simp only [h, List.mem_singleton] at hr
        subst hr
        rcases List.mem_append.mp hy with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inr h')
    | some c =>
      simp only [List.mem_filterMap] at hr
      obtain ⟨n, _, hn⟩ := hr
      cases h1 : rowOfG fpre (some f) fsuf n with
      | none => simp [h1] at hn
      | some fs =>
        cases h2 : rowOfG pre₂ (some c) suf₂ n with
        | none => simp [h1, h2] at hn
        | some us =>
          simp only [h1, h2, Option.some.injEq] at hn
          subst hn
          exact rowOfG_mem h2 y hy

/-- A test that implies a test, at the right positions that satisfy `U`, keeps `allZipT`. -/
theorem allZipT_imp {X Y : Type} {T T' : X → Y → Bool} {U : Y → Prop}
    (hT : ∀ x y, U y → T x y = true → T' x y = true) :
    ∀ {r₁ : List X} {r₂ : List Y}, (∀ y ∈ r₂, U y) → allZipT T r₁ r₂ = true →
      allZipT T' r₁ r₂ = true
  | x :: r₁, y :: r₂, hU, h => by
      simp only [allZipT, Bool.and_eq_true] at h ⊢
      exact ⟨hT x y (hU y List.mem_cons_self) h.1,
        allZipT_imp hT (fun y' hy' => hU y' (List.mem_cons_of_mem _ hy')) h.2⟩
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl

/-- **Aligned rows keep their answer `true`** under a test that implies a test, at the right
    positions that satisfy `U`. -/
theorem alignedAll_imp {X Y : Type} {T T' : X → Y → Bool} {U : Y → Prop}
    (hT : ∀ x y, U y → T x y = true → T' x y = true) {fpre fsuf : List X} {fsp : Option X}
    {pre₂ suf₂ : List Y} {sp₂ : Option Y} (hU : ∀ y ∈ pre₂, U y) (hU' : ∀ y, sp₂ = some y → U y)
    (hU'' : ∀ y ∈ suf₂, U y)
    (h : alignedAll (allZipT T) fpre fsp fsuf pre₂ sp₂ suf₂ = true) :
    alignedAll (allZipT T') fpre fsp fsuf pre₂ sp₂ suf₂ = true := by
  unfold alignedAll at h ⊢
  refine List.all_eq_true.mpr fun r hr => allZipT_imp hT (fun y hy => ?_)
    (List.all_eq_true.mp h r hr)
  rcases alignedRows_snd_mem hr y hy with h' | h' | h'
  · exact hU _ h'
  · exact hU' _ h'
  · exact hU'' _ h'

/-! ## The fuel of agreement is adequate -/

section Adequacy
variable {B : Sig} [Mean B] [Leaf B] {NL NR : Nat} {sL : Fin NL → Graph B NL}
  {sR : Fin NR → Graph B NR} (o : Orient) (ι : Fin NL → Fin NR → Bool)

omit [Mean B] [Leaf B] in
/-- A pair below a guard with a closed left side runs the row at the same fuel. -/
theorem pairX_noLeaf {prev : Tbl NL NR → Graph B NL → Graph B NR → Bool} {A : Tbl NL NR}
    {t : Graph B NL} {self : Graph B NR → Bool} (ht : NoLeaf t) (u : Graph B NR) :
    pairX (sL := sL) (sR := sR) prev A t self u = self u := by
  cases t with
  | leaf j => exact absurd ht (not_noLeaf_leaf j)
  | node op a => rfl

omit [Mean B] [Leaf B] in
/-- The right rows of a term with no leaf read no restart. -/
theorem rightC_noLeaf {restart restart' fam fam' : Graph B NR → Bool}
    (hf : ∀ y', NoLeaf y' → fam y' = fam' y') :
    ∀ y : Graph B NR, NoLeaf y → rightC sR restart fam y = rightC sR restart' fam' y := by
  intro y
  induction y with
  | leaf j => intro h; exact absurd h (not_noLeaf_leaf j)
  | node op a ih =>
    intro h
    cases op with
    | never => rfl
    | refine q qA =>
      simp only [rightC]
      rw [hf _ h, ih () (noLeaf_child h ())]
    | union m =>
      simp only [rightC]
      rw [hf _ h]
      congr 1
      exact congrArg (List.all _) (funext fun p => ih p (noLeaf_child h p))
    | prim g => exact hf _ h
    | set => exact hf _ h
    | list _ _ _ => exact hf _ h
    | obj _ _ _ => exact hf _ h
    | opaq => exact hf _ h
    | held _ _ _ => exact hf _ h
    | legacy _ => exact hf _ h

omit [Mean B] [Leaf B] in
/-- The slot of an object of terms with no leaf has no leaf. -/
theorem slotAtG_noLeaf {N : Nat} {fs : Finset String} {md : {x // x ∈ fs} → SlotMode B} {w : Fin 2}
    {b : (TOp.obj fs md w (B := B)).Pos → Graph B N} (hb : ∀ q, NoLeaf (b q)) (k : String) :
    NoLeaf (slotAtG (md := md) b k).2 := by
  unfold slotAtG
  split
  · exact hb _
  · match w, b, hb with
    | ⟨0, _⟩, _, _ => exact noLeaf_never _
    | ⟨1, _⟩, b, hb => exact hb _

omit [Mean B] [Leaf B] in
/-- The open block of an object of terms with no leaf has no leaf. -/
theorem blockG_noLeaf {N : Nat} {fs : Finset String} {md : {x // x ∈ fs} → SlotMode B} {w : Fin 2}
    {b : (TOp.obj fs md w (B := B)).Pos → Graph B N} (hb : ∀ q, NoLeaf (b q)) :
    NoLeaf (blockG (md := md) w b) := by
  match w, b, hb with
  | ⟨0, _⟩, _, _ => exact noLeaf_never _
  | ⟨1, _⟩, b, hb => exact hb _

omit [Mean B] [Leaf B] in
/-- The test of a slot gives one answer at each pair of tests that agree at the terms with no leaf. -/
theorem slotK_congr {fs : Finset String} {md : {x // x ∈ fs} → SlotMode B} {s : Fin 2}
    {kid kid' : (TOp.obj fs md s).Pos → Graph B NR → Bool}
    (hk : ∀ p u, NoLeaf u → kid p u = kid' p u) (k : String) (u : Graph B NR) (hu : NoLeaf u) :
    slotK kid k u = slotK kid' k u := by
  unfold slotK
  split
  · exact hk _ _ hu
  · match s with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => exact hk _ _ hu

omit [Mean B] [Leaf B] in
/-- The test of an open block gives one answer at each pair of tests that agree at the terms with no leaf. -/
theorem blockK_congr {fs : Finset String} {md : {x // x ∈ fs} → SlotMode B} (s : Fin 2)
    {kid kid' : (TOp.obj fs md s).Pos → Graph B NR → Bool}
    (hk : ∀ p u, NoLeaf u → kid p u = kid' p u) (u : Graph B NR) (hu : NoLeaf u) :
    blockK (md := md) s kid u = blockK (md := md) s kid' u := by
  match s, kid, kid', hk with
  | ⟨0, _⟩, _, _, _ => rfl
  | ⟨1, _⟩, kid, kid', hk => exact hk _ _ hu

omit [Mean B] [Leaf B] in
/-- **Two objects of closed terms agree alike at each walk of the positions.** -/
theorem objK_congr {fs : Finset String} {md : {x // x ∈ fs} → SlotMode B} {s : Fin 2}
    (a : (TOp.obj fs md s).Pos → Graph B NL)
    {kid kid' : (TOp.obj fs md s).Pos → Graph B NR → Bool}
    (hk : ∀ p u, NoLeaf u → kid p u = kid' p u) (y : Graph B NR) (hy : NoLeaf y) :
    objK (md := md) o a kid y = objK (md := md) o a kid' y := by
  cases y with
  | leaf j => exact absurd hy (not_noLeaf_leaf j)
  | node op b =>
    cases op with
    | obj fs' md' s' =>
      have hb : ∀ q, NoLeaf (b q) := fun q => noLeaf_child hy q
      have e1 : ∀ x : {x // x ∈ fs}, kid (Sum.inl x) (slotAtG (md := md') b x.1).2 =
          kid' (Sum.inl x) (slotAtG (md := md') b x.1).2 := fun x => hk _ _ (slotAtG_noLeaf hb x.1)
      have e2 : ∀ x : {x // x ∈ fs'}, slotK kid x.1 (b (Sum.inl x)) = slotK kid' x.1 (b (Sum.inl x)) :=
        fun x => slotK_congr hk _ _ (hb _)
      have e3 := blockK_congr (md := md) s hk _ (blockG_noLeaf (md := md') hb)
      simp only [objK, e1, e2, e3]
    | _ => rfl

omit [Mean B] [Leaf B] in
/-- **The family of two closed terms agrees at each walk of the positions.** -/
theorem famN_congr (op : TOp B) (a : op.Pos → Graph B NL)
    {kid kid' : op.Pos → Graph B NR → Bool} (hk : ∀ p u, NoLeaf u → kid p u = kid' p u)
    (y : Graph B NR) (hy : NoLeaf y) : famN o op a kid y = famN o op a kid' y := by
  cases y with
  | leaf j => exact absurd hy (not_noLeaf_leaf j)
  | node op' b =>
    cases op with
    | held s k₀ ks =>
      cases op' with
      | held s' k₀' ks' =>
        exact congrArg (fun t => decide ((⟨s, k₀ :: ks⟩ : (s : Bool) × List (B.G s × Bool)) =
          ⟨s', k₀' :: ks'⟩) && t) (hk true _ (noLeaf_child hy true))
      | _ => rfl
    | set =>
      cases op' with
      | set => exact hk () _ (noLeaf_child hy ())
      | _ => rfl
    | list n s m =>
      cases op' with
      | list n' s' m' =>
        have hU : ∀ u, (u ∈ (listParts b).1 ∨ (listParts b).2.1 = some u ∨
            u ∈ (listParts b).2.2) → NoLeaf u :=
          fun u h => by obtain ⟨q, rfl⟩ := mem_listParts b h; exact noLeaf_child hy q
        exact Bool.eq_iff_iff.mpr
          ⟨alignedAll_imp (U := NoLeaf) (fun p u hu h0 => (hk p u hu) ▸ h0)
            (fun u h => hU u (Or.inl h)) (fun u h => hU u (Or.inr (Or.inl h)))
            (fun u h => hU u (Or.inr (Or.inr h))),
          alignedAll_imp (U := NoLeaf) (fun p u hu h0 => (hk p u hu).symm ▸ h0)
            (fun u h => hU u (Or.inl h)) (fun u h => hU u (Or.inr (Or.inl h)))
            (fun u h => hU u (Or.inr (Or.inr h)))⟩
      | _ => rfl
    | obj fs md s => exact objK_congr o a hk _ hy
    | _ => rfl

variable (sL sR)

/-- **A pair of terms with no leaf reads no restart**: the row answers the same at each walk. -/
theorem goW_noLeaf (prev prev' : Tbl NL NR → Graph B NL → Graph B NR → Bool) (A : Tbl NL NR) :
    ∀ x : Graph B NL, NoLeaf x → ∀ y : Graph B NR, NoLeaf y →
      goW (rowSpecC sL sR o ι) prev A x y = goW (rowSpecC sL sR o ι) prev' A x y := by
  intro x
  induction x with
  | leaf j => intro h; exact absurd h (not_noLeaf_leaf j)
  | node op a ih =>
    intro hx y hy
    have hk : ∀ (p : op.Pos) (u : Graph B NR), NoLeaf u →
        pairX (sL := sL) (sR := sR) prev A (a p) (goW (rowSpecC sL sR o ι) prev A (a p)) u =
        pairX (sL := sL) (sR := sR) prev' A (a p) (goW (rowSpecC sL sR o ι) prev' A (a p)) u := by
      intro p u hu
      rw [pairX_noLeaf (noLeaf_child hx p), pairX_noLeaf (noLeaf_child hx p)]
      exact ih p (noLeaf_child hx p) u hu
    cases op with
    | never => rfl
    | refine q qA =>
      exact congrArg (fun t => cbaseG sL sR o (.node (.refine q qA) a) y || t)
        (ih () (noLeaf_child hx ()) y hy)
    | union m =>
      exact congrArg (fun t => cbaseG sL sR o (.node (.union m) a) y || t)
        (congrArg (List.all _) (funext fun p => ih p (noLeaf_child hx p) y hy))
    | prim g => exact rightC_noLeaf (fun y' _ => rfl) y hy
    | opaq => exact rightC_noLeaf (fun y' _ => rfl) y hy
    | legacy r => exact rightC_noLeaf (fun y' _ => rfl) y hy
    | held s k₀ ks =>
      exact rightC_noLeaf (fun y' hy' => congrArg (fun t => cbaseG sL sR o _ y' || t)
        (famN_congr o (.held s k₀ ks) a hk y' hy')) y hy
    | set =>
      exact rightC_noLeaf (fun y' hy' => congrArg (fun t => cbaseG sL sR o _ y' || t)
        (famN_congr o .set a hk y' hy')) y hy
    | list n s m =>
      exact rightC_noLeaf (fun y' hy' => congrArg (fun t => cbaseG sL sR o _ y' || t)
        (famN_congr o (.list n s m) a hk y' hy')) y hy
    | obj fs md s =>
      exact rightC_noLeaf (fun y' hy' => congrArg (fun t => cbaseG sL sR o _ y' || t)
        (famN_congr o (.obj fs md s) a hk y' hy')) y hy

variable {sL sR}

omit [Mean B] [Leaf B] in
/-- The test of a slot keeps its answer `true` under tests that imply tests. -/
theorem slotK_mono {fs : Finset String} {md : {x // x ∈ fs} → SlotMode B} {s : Fin 2}
    {kid kid' : (TOp.obj fs md s).Pos → Graph B NR → Bool}
    (hk : ∀ p, TestMono LeafOrNever (kid p) (kid' p)) (k : String) (u : Graph B NR)
    (hu : LeafOrNever u) : slotK kid k u = true → slotK kid' k u = true := by
  unfold slotK
  split
  · exact hk _ _ hu
  · match s with
    | ⟨0, _⟩ => exact fun h => h
    | ⟨1, _⟩ => exact hk _ _ hu

omit [Mean B] [Leaf B] in
/-- The test of an open block keeps its answer `true` under tests that imply tests. -/
theorem blockK_mono {fs : Finset String} {md : {x // x ∈ fs} → SlotMode B} (s : Fin 2)
    {kid kid' : (TOp.obj fs md s).Pos → Graph B NR → Bool}
    (hk : ∀ p, TestMono LeafOrNever (kid p) (kid' p)) (u : Graph B NR) (hu : LeafOrNever u) :
    blockK (md := md) s kid u = true → blockK (md := md) s kid' u = true := by
  match s, kid, kid', hk with
  | ⟨0, _⟩, _, _, _ => exact fun h => h
  | ⟨1, _⟩, kid, kid', hk => exact hk _ _ hu

omit [Mean B] [Leaf B] in
/-- The open block of an object of entries is an entry or the bottom. -/
theorem blockG_leafOrNever {fs : Finset String} {md : {x // x ∈ fs} → SlotMode B} {w : Fin 2}
    {b : (TOp.obj fs md w (B := B)).Pos → Graph B NR} (hb : ∀ q, ∃ j, b q = .leaf j) :
    LeafOrNever (blockG (md := md) w b) := by
  match w, b, hb with
  | ⟨0, _⟩, _, _ => exact Or.inr ⟨(fun p => nomatch p), rfl⟩
  | ⟨1, _⟩, b, hb => obtain ⟨j, hj⟩ := hb (.inr ⟨0, Nat.one_pos⟩); exact Or.inl ⟨j, hj⟩

omit [Mean B] [Leaf B] in
/-- **Two objects keep their answer `true`** under tests that imply tests. -/
theorem objK_mono {fs : Finset String} {md : {x // x ∈ fs} → SlotMode B} {s : Fin 2}
    (a : (TOp.obj fs md s).Pos → Graph B NL)
    {kid kid' : (TOp.obj fs md s).Pos → Graph B NR → Bool}
    (hk : ∀ p, TestMono LeafOrNever (kid p) (kid' p)) {fs' : Finset String}
    {md' : {x // x ∈ fs'} → SlotMode B} {s' : Fin 2} {b : (TOp.obj fs' md' s' (B := B)).Pos → Graph B NR}
    (hb : ∀ q, ∃ j, b q = .leaf j)
    (h : objK (md := md) o a kid (.node (.obj fs' md' s') b) = true) :
    objK (md := md) o a kid' (.node (.obj fs' md' s') b) = true := by
  simp only [objK, Bool.and_eq_true, List.all_eq_true] at h ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨⟨fun x hx => ?_, fun x hx => ?_⟩, ?_⟩
  · exact ⟨(h1 x hx).1, hk _ _ (slotAtG_leafOrNever hb x.1) (h1 x hx).2⟩
  · obtain ⟨j, hj⟩ := hb (.inl x)
    exact ⟨(h2 x hx).1, slotK_mono hk _ _ (Or.inl ⟨j, hj⟩) (h2 x hx).2⟩
  · exact blockK_mono s hk _ (blockG_leafOrNever hb) h3

variable (sL sR)

/-- **The invariant of a term in a system of agreement**: flat, with no leaf below a wall. -/
def Ok {N : Nat} (t : Graph B N) : Prop := Flat1 t = true ∧ Good t

/-- **The bottom answers `true` against each term.** -/
theorem cbaseG_never (x : Graph B NL) (a' : (TSig B).Pos TOp.never → Graph B NR) :
    cbaseG sL sR o x (.node .never a') = true := by
  simp [cbaseG, isNeverG]

/-- **A left entry against the bottom answers `true`.** -/
theorem goW_leaf_never (prev : Tbl NL NR → Graph B NL → Graph B NR → Bool) (A : Tbl NL NR)
    (i : Fin NL) (a' : (TSig B).Pos TOp.never → Graph B NR) :
    goW (rowSpecC sL sR o ι) prev A (.leaf i) (.node .never a') = true := by
  change ((cbaseG sL sR o (.leaf i) (.node .never a') || oneG ι i (.node .never a')) ||
    prev A (sL i) (.node .never a')) = true
  exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.or_eq_true_iff.mpr (Or.inl (cbaseG_never sL sR o _ a'))))

/-- **The row of agreement answers `true` against the bottom.** -/
theorem rowNever_C (ρL : Fin NL → Nat) : RowNever ρL (rowSpecC sL sR o ι) := by
  intro prev n _ A x a' _
  cases x with
  | leaf j => exact goW_leaf_never sL sR o ι prev A j a'
  | node op b =>
    cases op with
    | never => rfl
    | refine q qA =>
      change (cbaseG sL sR o (.node (.refine q qA) b) (.node .never a') ||
        goW (rowSpecC sL sR o ι) prev A (b ()) (.node .never a')) = true
      exact Bool.or_eq_true_iff.mpr (Or.inl (cbaseG_never sL sR o _ a'))
    | union m =>
      change (cbaseG sL sR o (.node (.union m) b) (.node .never a') ||
        (List.finRange m).all fun p => goW (rowSpecC sL sR o ι) prev A (b p) (.node .never a')) = true
      exact Bool.or_eq_true_iff.mpr (Or.inl (cbaseG_never sL sR o _ a'))
    | prim _ => rfl
    | set => rfl
    | list _ _ _ => rfl
    | obj _ _ _ => rfl
    | opaq => rfl
    | held _ _ _ => rfl
    | legacy _ => rfl


variable (ρL : Fin NL → Nat) (ρR : Fin NR → Nat)

/-- **The row of agreement keeps its answer `true`** from a walk to a walk at the calls that the
    measure bounds. The terms hold no leaf below a wall. -/
theorem rowMono_C (F : Fueled sL sR ρL ρR) (hgL : ∀ i, Good (sL i)) (hgR : ∀ j, Good (sR j)) :
    RowMono ρL ρR Ok Ok (rowSpecC sL sR o ι) := by
  intro prev prev' m hM hN A
  have key : ∀ x : Graph B NL, Flat1 x = true → Good x → ∀ y : Graph B NR, Flat1 y = true → Good y →
      phi ρL ρR A x y ≤ m → goW (rowSpecC sL sR o ι) prev A x y = true →
        goW (rowSpecC sL sR o ι) prev' A x y = true := by
    intro x
    induction x with
    | leaf j =>
      intro hx hg y hy hgy hφ h
      have h1 := le_hgt_leaf (B := B) ρL j
      have h2 := hgt_entry (B := B) (sys := sL) F.edgeL j
      change ((cbaseG sL sR o (.leaf j) y || oneG ι j y) || prev A (sL j) y) = true at h
      change ((cbaseG sL sR o (.leaf j) y || oneG ι j y) || prev' A (sL j) y) = true
      rcases Bool.or_eq_true_iff.mp h with h | h
      · exact Bool.or_eq_true_iff.mpr (Or.inl h)
      · refine Bool.or_eq_true_iff.mpr (Or.inr (hM A (sL j) y ⟨F.flatL j, hgL j⟩ ⟨hy, hgy⟩ ?_ h))
        unfold phi at hφ ⊢
        omega
    | node op a ih =>
      intro hx hg y hy hgy hφ h
      have hbud : budget NL NR A ≤ m := by unfold phi at hφ; omega
      have hr : ∀ j, y.ulv (TSig B) j = true → prev A (.node op a) (sR j) = true →
          prev' A (.node op a) (sR j) = true := by
        intro j hj hp
        have h1 := le_hgt (ρ := ρR) hj
        have h2 := hgt_entry (B := B) (sys := sR) F.edgeR j
        refine hM A _ (sR j) ⟨hx, hg⟩ ⟨F.flatR j, hgR j⟩ ?_ hp
        unfold phi at hφ ⊢
        omega
      have hU := fun (op : TOp B) (a : op.Pos → Graph B NR) (p : op.Pos) (hk : TOp.kind op ≠ .wall)
        (hg : Good (.node op a)) => good_child hg hk p
      have hleaf : ∀ i a', goW (rowSpecC sL sR o ι) prev' A (.leaf i) (.node .never a') = true :=
        fun i a' => goW_leaf_never sL sR o ι prev' A i a'
      cases op with
      | never => rfl
      | refine q qA =>
        change (cbaseG sL sR o (.node (.refine q qA) a) y ||
          goW (rowSpecC sL sR o ι) prev A (a ()) y) = true at h
        change (cbaseG sL sR o (.node (.refine q qA) a) y ||
          goW (rowSpecC sL sR o ι) prev' A (a ()) y) = true
        rcases Bool.or_eq_true_iff.mp h with h | h
        · exact Bool.or_eq_true_iff.mpr (Or.inl h)
        · refine Bool.or_eq_true_iff.mpr (Or.inr (ih () (flat1_keep rfl hx ())
            (good_child hg (fun hk => nomatch hk) ()) y hy hgy ?_ h))
          have := hgt_child ρL a (o := TOp.refine q qA) rfl ()
          unfold phi at hφ ⊢
          omega
      | union k =>
        change (cbaseG sL sR o (.node (.union k) a) y ||
          (List.finRange k).all fun p => goW (rowSpecC sL sR o ι) prev A (a p) y) = true at h
        change (cbaseG sL sR o (.node (.union k) a) y ||
          (List.finRange k).all fun p => goW (rowSpecC sL sR o ι) prev' A (a p) y) = true
        rcases Bool.or_eq_true_iff.mp h with h | h
        · exact Bool.or_eq_true_iff.mpr (Or.inl h)
        · refine Bool.or_eq_true_iff.mpr (Or.inr (List.all_eq_true.mpr fun p hp => ?_))
          refine ih p (flat1_keep rfl hx p) (good_child hg (fun hk => nomatch hk) p) y hy hgy ?_
            (List.all_eq_true.mp h p hp)
          have := hgt_child ρL a (o := TOp.union k) rfl p
          unfold phi at hφ ⊢
          omega
      | prim g =>
        refine rightC_mono_u sR Good hU (fun y' _ _ hfam => ?_) y hy hgy hr h
        rcases Bool.or_eq_true_iff.mp hfam with hc | hm
        · exact Bool.or_eq_true_iff.mpr (Or.inl hc)
        · exact nomatch hm
      | opaq =>
        refine rightC_mono_u sR Good hU (fun y' _ _ hfam => ?_) y hy hgy hr h
        rcases Bool.or_eq_true_iff.mp hfam with hc | hm
        · exact Bool.or_eq_true_iff.mpr (Or.inl hc)
        · exact nomatch hm
      | legacy r =>
        refine rightC_mono_u sR Good hU (fun y' _ _ hfam => ?_) y hy hgy hr h
        rcases Bool.or_eq_true_iff.mp hfam with hc | hm
        · exact Bool.or_eq_true_iff.mpr (Or.inl hc)
        · exact nomatch hm
      | held s k₀ ks =>
        refine rightC_mono_u sR Good hU (fun y' hy'1 hy'g hfam => ?_) y hy hgy hr h
        rcases Bool.or_eq_true_iff.mp hfam with hc | hm
        · exact Bool.or_eq_true_iff.mpr (Or.inl hc)
        · refine Bool.or_eq_true_iff.mpr (Or.inr ?_)
          cases y' with
          | leaf _ => exact nomatch hm
          | node op' b =>
            cases op' with
            | held s' k₀' ks' =>
              have cla : NoLeaf (a true) := noLeaf_wall hg rfl true
              have clb : NoLeaf (b true) := noLeaf_wall hy'g rfl true
              have e : pairX (sL := sL) (sR := sR) prev A (a true)
                  (goW (rowSpecC sL sR o ι) prev A (a true)) (b true) =
                  pairX (sL := sL) (sR := sR) prev' A (a true)
                  (goW (rowSpecC sL sR o ι) prev' A (a true)) (b true) := by
                rw [pairX_noLeaf cla, pairX_noLeaf cla]
                exact goW_noLeaf sL sR o ι prev prev' A _ cla _ clb
              change (decide ((⟨s, k₀ :: ks⟩ : (s : Bool) × List (B.G s × Bool)) = ⟨s', k₀' :: ks'⟩) &&
                pairX (sL := sL) (sR := sR) prev' A (a true)
                  (goW (rowSpecC sL sR o ι) prev' A (a true)) (b true)) = true
              rw [← e]
              exact hm
            | _ => exact nomatch hm
      | set =>
        obtain ⟨i, hi⟩ := flat1_down (o := TOp.set) rfl hx ()
        refine rightC_mono_u sR Good hU (fun y' hy'1 hy'g hfam => ?_) y hy hgy hr h
        rcases Bool.or_eq_true_iff.mp hfam with hc | hm
        · exact Bool.or_eq_true_iff.mpr (Or.inl hc)
        · refine Bool.or_eq_true_iff.mpr (Or.inr ?_)
          cases y' with
          | leaf _ => exact nomatch hm
          | node op' b =>
            cases op' with
            | set =>
              obtain ⟨j, hj⟩ := flat1_down (o := TOp.set) rfl hy'1 ()
              change pairX (sL := sL) (sR := sR) prev' A (a ())
                (goW (rowSpecC sL sR o ι) prev' A (a ())) (b ()) = true
              have hm' : pairX (sL := sL) (sR := sR) prev A (a ())
                (goW (rowSpecC sL sR o ι) prev A (a ())) (b ()) = true := hm
              rw [hi] at hm' ⊢
              exact pairX_mono_gen sL sR ρL ρR F (fun i => ⟨F.flatL i, hgL i⟩)
                (fun j => ⟨F.flatR j, hgR j⟩) hM hbud i (b ()) (Or.inl ⟨j, hj⟩) _ _
                (fun a' => hleaf i a') hm'
            | _ => exact nomatch hm
      | list n s k =>
        have hdown := fun q => flat1_down (o := TOp.list n s k) rfl hx q
        refine rightC_mono_u sR Good hU (fun y' hy'1 hy'g hfam => ?_) y hy hgy hr h
        rcases Bool.or_eq_true_iff.mp hfam with hc | hm
        · exact Bool.or_eq_true_iff.mpr (Or.inl hc)
        · refine Bool.or_eq_true_iff.mpr (Or.inr ?_)
          cases y' with
          | leaf _ => exact nomatch hm
          | node op' b =>
            cases op' with
            | list n' s' k' =>
              have hbd := fun q => flat1_down (o := TOp.list n' s' k') rfl hy'1 q
              have hU : ∀ u, (u ∈ (listParts b).1 ∨ (listParts b).2.1 = some u ∨
                  u ∈ (listParts b).2.2) → LeafOrNever u := fun u h => by
                obtain ⟨q, rfl⟩ := mem_listParts b h
                obtain ⟨j, hj⟩ := hbd q
                exact Or.inl ⟨j, hj⟩
              refine alignedAll_imp (U := LeafOrNever) (fun p u hu h0 => ?_)
                (fun u h => hU u (Or.inl h)) (fun u h => hU u (Or.inr (Or.inl h)))
                (fun u h => hU u (Or.inr (Or.inr h))) hm
              obtain ⟨i, hi⟩ := hdown p
              have h0' : pairX (sL := sL) (sR := sR) prev A (a p)
                  (goW (rowSpecC sL sR o ι) prev A (a p)) u = true := h0
              show pairX (sL := sL) (sR := sR) prev' A (a p)
                (goW (rowSpecC sL sR o ι) prev' A (a p)) u = true
              rw [hi] at h0' ⊢
              exact pairX_mono_gen sL sR ρL ρR F (fun i => ⟨F.flatL i, hgL i⟩)
                (fun j => ⟨F.flatR j, hgR j⟩) hM hbud i u hu _ _ (fun a' => hleaf i a') h0'
            | _ => exact nomatch hm
      | obj fs md w =>
        have hdown := fun q => flat1_down (o := TOp.obj fs md w) rfl hx q
        refine rightC_mono_u sR Good hU (fun y' hy'1 hy'g hfam => ?_) y hy hgy hr h
        rcases Bool.or_eq_true_iff.mp hfam with hc | hm
        · exact Bool.or_eq_true_iff.mpr (Or.inl hc)
        · refine Bool.or_eq_true_iff.mpr (Or.inr ?_)
          cases y' with
          | leaf _ => exact nomatch hm
          | node op' b =>
            cases op' with
            | obj fs' md' w' =>
              have hbd := fun q => flat1_down (o := TOp.obj fs' md' w') rfl hy'1 q
              refine objK_mono (md := md) o a (kid := fun p => pairX (sL := sL) (sR := sR) prev A (a p)
                (goW (rowSpecC sL sR o ι) prev A (a p))) (kid' := fun p => pairX (sL := sL) (sR := sR) prev' A (a p)
                (goW (rowSpecC sL sR o ι) prev' A (a p))) (fun p => ?_) hbd hm
              intro u hu h0
              obtain ⟨i, hi⟩ := hdown p
              have h0' : pairX (sL := sL) (sR := sR) prev A (a p)
                  (goW (rowSpecC sL sR o ι) prev A (a p)) u = true := h0
              show pairX (sL := sL) (sR := sR) prev' A (a p)
                (goW (rowSpecC sL sR o ι) prev' A (a p)) u = true
              rw [hi] at h0' ⊢
              exact pairX_mono_gen sL sR ρL ρR F (fun i => ⟨F.flatL i, hgL i⟩)
                (fun j => ⟨F.flatR j, hgR j⟩) hM hbud i u hu _ _ (fun a' => hleaf i a') h0'
            | _ => exact nomatch hm
  intro x y hx hy hφ h
  exact key x hx.1 hx.2 y hy.1 hy.2 hφ h

/-- **The fuel of agreement is adequate**: where the optimistic walk of agreement answers `true` at
    the fuel of `disjoint`, so does the walk. -/
theorem compO_fuel_imp_compG (F : Fueled sL sR ρL ρR) (hgL : ∀ i, Good (sL i)) (hgR : ∀ j, Good (sR j))
    (A : Tbl NL NR) (rL : Fin NL) (rR : Fin NR)
    (h : walkO (rowSpecC sL sR o ι) (fuel NL NR) A (.leaf rL) (.leaf rR) = true) :
    compG sL sR o ι (fuel NL NR) A (.leaf rL) (.leaf rR) = true :=
  walkO_fuel_imp_walk sL sR ρL ρR F (rowMono_C sL sR o ι ρL ρR F hgL hgR) (rowNever_C sL sR o ι ρL) A rL rR
    ⟨rfl, fun _ => rfl⟩ ⟨rfl, fun _ => rfl⟩ h

end Adequacy

/-- **The fuel of `compat` is adequate**: where the optimistic walk of agreement answers `true` at the
    root, so does `compat`. -/
theorem compat_of_compO [Mean B] [Leaf B] {NL NR : Nat} (o : Orient) (ι : Fin NL → Fin NR → Bool)
    (dL : Closed B NL) (dR : Closed B NR) (rL : Fin NL) (rR : Fin NR)
    (h : walkO (rowSpecC dL.graph dR.graph o ι) (fuel NL NR) (diagTbl ι) (.leaf rL) (.leaf rR) = true) :
    compat o ι dL rL dR rR = true :=
  compO_fuel_imp_compG dL.graph dR.graph o ι (fun i => i.val) (fun j => j.val) (Closed.fueled dL dR)
    (Closed.good_graph dL) (Closed.good_graph dR) (diagTbl ι) rL rR h

end Calculus.Alg.Scoped
