import Calculus.Lang.ScopeDisjoint

/-!
# The fuel of the decision is adequate

`decG` answers `false` when its fuel runs out, and `decO` answers `true` there. `decO` is at least
`decG` at every fuel. Over a flat guarded system, the two agree at the fuel of `disjoint`: a call
of the walk lowers a measure, so no explored path reaches an empty fuel.

The measure of a call is the number of table entries still free, scaled by the unguarded steps
between two guards, plus the unguarded heights of the two terms. A flat system has a rank that
every unguarded edge lowers, and that rank bounds each height.
-/

namespace Calculus.Alg.Scoped

section Fuel
variable {B : Sig} [Leaf B]

/-- **The walk whose empty fuel answers `true`.** -/
def walkO {NL NR : Nat} {sL : Fin NL → Graph B NL} {sR : Fin NR → Graph B NR} (R : Row sL sR) :
    Nat → Tbl NL NR → Graph B NL → Graph B NR → Bool
  | 0 => fun _ _ _ => true
  | n + 1 => goW R (walkO R n)

/-- **The walk of disjointness whose empty fuel answers `true`.** -/
def decO {NL NR : Nat} (sL : Fin NL → Graph B NL) (sR : Fin NR → Graph B NR) :
    Nat → Tbl NL NR → Graph B NL → Graph B NR → Bool := walkO (rowSpecG sL sR)

/-- **A flat term**: a container holds an entry at each position, and a wall holds a closed term
    that the walk does not read. -/
def Flat1 {N : Nat} : Graph B N → Bool
  | .leaf _ => true
  | .node o a => match (TSig B).kind o with
    | .keep => ((TSig B).pos o).attach.all fun p => Flat1 (a p.1)
    | .down => ((TSig B).pos o).all fun p => match a p with
      | .leaf _ => true
      | _ => false
    | .wall => true

/-- **The unguarded height of a term**: the highest rank of an entry at an unguarded position. -/
def hgt {N : Nat} (ρ : Fin N → Nat) (t : Graph B N) : Nat :=
  (List.finRange N).foldr (fun j m => max (if t.ulv (TSig B) j then ρ j + 1 else 0) m) 0

omit [Leaf B] in
/-- A flat term whose operation keeps the positions has flat terms at its positions. -/
theorem flat1_keep {N : Nat} {o : TOp B} {a : (TSig B).Pos o → Graph B N}
    (ho : (TSig B).kind o = .keep) (h : Flat1 (.node o a) = true) (p : (TSig B).Pos o) :
    Flat1 (a p) = true := by
  unfold Flat1 at h
  rw [ho] at h
  exact List.all_eq_true.mp h ⟨p, (TSig B).pos_complete o p⟩ (List.mem_attach _ _)

omit [Leaf B] in
/-- A flat term whose operation guards the positions has an entry at each position. -/
theorem flat1_down {N : Nat} {o : TOp B} {a : (TSig B).Pos o → Graph B N}
    (ho : (TSig B).kind o = .down) (h : Flat1 (.node o a) = true) (p : (TSig B).Pos o) :
    ∃ j, a p = .leaf j := by
  unfold Flat1 at h
  rw [ho] at h
  have := List.all_eq_true.mp h p ((TSig B).pos_complete o p)
  cases hp : a p with
  | leaf j => exact ⟨j, rfl⟩
  | node _ _ => rw [hp] at this; exact nomatch this

omit [Leaf B] in
/-- An unguarded leaf of a position is an unguarded leaf of the term. -/
theorem ulv_keep {N : Nat} {o : TOp B} {a : (TSig B).Pos o → Graph B N} {j : Fin N}
    (ho : (TSig B).kind o = .keep) (p : (TSig B).Pos o) (h : (a p).ulv (TSig B) j = true) :
    (Flat.node o a : Graph B N).ulv (TSig B) j = true := by
  show Flat.ulv (TSig B) j (.node o a) = true
  unfold Flat.ulv
  rw [ho]
  exact List.any_eq_true.mpr ⟨p, (TSig B).pos_complete o p, h⟩

omit [Leaf B] in
/-- An entry at an unguarded position of a term is below the height of the term. -/
theorem le_hgt {N : Nat} {ρ : Fin N → Nat} {t : Graph B N} {j : Fin N}
    (h : t.ulv (TSig B) j = true) : ρ j + 1 ≤ hgt ρ t := by
  unfold hgt
  have key : ∀ l : List (Fin N), j ∈ l →
      ρ j + 1 ≤ l.foldr (fun j m => max (if t.ulv (TSig B) j then ρ j + 1 else 0) m) 0 := by
    intro l
    induction l with
    | nil => intro hj; exact nomatch hj
    | cons a l ih =>
      intro hj
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp hj with rfl | hj
      · rw [if_pos h]; exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih hj) (Nat.le_max_right _ _)
  exact key _ (List.mem_finRange j)

omit [Leaf B] in
/-- A height below a bound, where each entry at an unguarded position is. -/
theorem hgt_le {N : Nat} {ρ : Fin N → Nat} {t : Graph B N} {c : Nat}
    (h : ∀ j, t.ulv (TSig B) j = true → ρ j + 1 ≤ c) : hgt ρ t ≤ c := by
  unfold hgt
  have key : ∀ l : List (Fin N),
      l.foldr (fun j m => max (if t.ulv (TSig B) j then ρ j + 1 else 0) m) 0 ≤ c := by
    intro l
    induction l with
    | nil => exact Nat.zero_le _
    | cons a l ih =>
      simp only [List.foldr_cons]
      refine Nat.max_le.mpr ⟨?_, ih⟩
      cases ha : t.ulv (TSig B) a
      · simp
      · simpa using h a ha
  exact key _


omit [Leaf B] in
/-- A child of a term whose operation keeps the unguarded positions has no higher height. -/
theorem hgt_child {N : Nat} (ρ : Fin N → Nat) {o : TOp B} (a : (TSig B).Pos o → Graph B N)
    (ho : (TSig B).kind o = .keep) (p : (TSig B).Pos o) :
    hgt ρ (a p) ≤ hgt ρ (.node o a) := by
  refine hgt_le fun j hj => le_hgt ?_
  show Flat.ulv (TSig B) j (.node o a) = true
  unfold Flat.ulv
  rw [ho]
  exact List.any_eq_true.mpr ⟨p, (TSig B).pos_complete o p, hj⟩

omit [Leaf B] in
/-- A term that is an entry has the height of the rank of the entry, plus one. -/
theorem le_hgt_leaf {N : Nat} (ρ : Fin N → Nat) (j : Fin N) :
    ρ j + 1 ≤ hgt ρ (.leaf j : Graph B N) :=
  le_hgt (by simp [Flat.ulv])

omit [Leaf B] in
/-- The body of an entry, where the rank lowers at each unguarded edge, is lower than the entry. -/
theorem hgt_entry {N : Nat} {ρ : Fin N → Nat} {sys : Fin N → Graph B N}
    (hρ : ∀ i j, (sys i).ulv (TSig B) j = true → ρ j < ρ i) (i : Fin N) :
    hgt ρ (sys i) ≤ ρ i :=
  hgt_le fun j hj => hρ i j hj

variable {NL NR : Nat} (sL : Fin NL → Graph B NL) (sR : Fin NR → Graph B NR)

/-- **A term below the bottom is separated from any term at a fuel above its height**, where the
    walk that the row reads answers so below the fuel. -/
theorem rowG_right_never {ρL : Fin NL → Nat} (hρ : ∀ i j, (sL i).ulv (TSig B) j = true → ρL j < ρL i)
    (prev : Tbl NL NR → Graph B NL → Graph B NR → Bool) (n : Nat)
    (hprev : ∀ A x a', hgt ρL x < n → prev A x (.node .never a') = true) :
    ∀ (A : Tbl NL NR) (x : Graph B NL) (a' : (TSig B).Pos TOp.never → Graph B NR),
      hgt ρL x < n + 1 → rowG sL sR prev A x (.node .never a') = true := by
  intro A x a'
  induction x with
  | leaf j =>
    intro h
    have h1 := le_hgt_leaf (B := B) ρL j
    have h2 := hgt_entry (B := B) hρ j
    exact hprev A (sL j) a' (by omega)
  | node op b ihb =>
    intro h
    cases op with
    | never => rfl
    | refine _ _ => exact ihb () (Nat.lt_of_le_of_lt (hgt_child ρL b rfl ()) h)
    | union m =>
      rw [rowG_union]
      exact List.all_eq_true.mpr fun p _ => ihb p (Nat.lt_of_le_of_lt (hgt_child ρL b rfl p) h)
    | prim _ => rfl
    | set => rfl
    | list _ _ _ => rfl
    | obj _ _ _ => rfl
    | opaq => rfl
    | held _ _ _ => rfl
    | legacy _ => rfl

section Mono
variable {X : Type}

/-- A test that implies another at the arguments that satisfy `U`. -/
def TestMono (U : X → Prop) (f f' : X → Bool) : Prop := ∀ u, U u → f u = true → f' u = true

omit [Leaf B] in
/-- **A zip that finds a disjoint position keeps it** under a test that implies another. -/
theorem anyZipG_mono {U : X → Prop} {fs fs' : List (X → Bool)}
    (hF : List.Forall₂ (TestMono U) fs fs') :
    ∀ {us : List X}, (∀ u ∈ us, U u) → anyZipG fs us = true → anyZipG fs' us = true := by
  induction hF with
  | nil => intro us _ h; exact h
  | cons hf _ ih =>
    intro us hU h
    cases us with
    | nil => exact nomatch h
    | cons u us =>
      simp only [anyZipG, Bool.or_eq_true] at h ⊢
      rcases h with h | h
      · exact Or.inl (hf u (hU u List.mem_cons_self) h)
      · exact Or.inr (ih (fun v hv => hU v (List.mem_cons_of_mem _ hv)) h)

/-- Each position of a row is a position that the shape declares. -/
theorem rowOfG_mem {α : Type} {pre suf : List α} {sp : Option α} {n : Nat} {row : List α}
    (h : rowOfG pre sp suf n = some row) : ∀ t ∈ row, t ∈ pre ∨ sp = some t ∨ t ∈ suf := by
  intro t ht
  cases sp with
  | none =>
    rw [rowOfG_none_eq] at h
    split at h
    · cases h
      rcases List.mem_append.mp ht with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · exact nomatch h
  | some c =>
    rw [rowOfG_some_eq] at h
    split at h
    · exact nomatch h
    · cases h
      rcases List.mem_append.mp ht with h | h
      · rcases List.mem_append.mp h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (by rw [(List.mem_replicate.mp h).2]))
      · exact Or.inr (Or.inr h)

/-- A spreading shape has a row exactly where its prefix and suffix fit. -/
theorem rowOfG_some_isSome {α : Type} (pre : List α) (c : α) (suf : List α) (n : Nat) :
    (rowOfG pre (some c) suf n).isSome = decide (pre.length + suf.length ≤ n) := by
  rw [rowOfG_some_eq]
  split
  · next h => simp; omega
  · next h => simp; omega

omit [Leaf B] in
/-- **The list row keeps its answer `true`** under tests that imply tests, at the arguments that
    the row reads. -/
theorem listRowG_mono {U : X → Prop} {fpre fpre' fsuf fsuf' : List (X → Bool)}
    {fsp fsp' : Option (X → Bool)} {pre₂ suf₂ : List X} {sp₂ : Option X}
    (hp : List.Forall₂ (TestMono U) fpre fpre')
    (hs : (fsp = none ∧ fsp' = none) ∨ ∃ f f', fsp = some f ∧ fsp' = some f' ∧ TestMono U f f')
    (hf : List.Forall₂ (TestMono U) fsuf fsuf')
    (hU : ∀ u ∈ pre₂, U u) (hU' : ∀ u, sp₂ = some u → U u) (hU'' : ∀ u ∈ suf₂, U u)
    (h : listRowG fpre fsp fsuf pre₂ sp₂ suf₂ = true) :
    listRowG fpre' fsp' fsuf' pre₂ sp₂ suf₂ = true := by
  have e1 : fpre'.length = fpre.length := hp.length_eq.symm
  have e2 : fsuf'.length = fsuf.length := hf.length_eq.symm
  have hrowU : ∀ {n : Nat} {us : List X}, rowOfG pre₂ sp₂ suf₂ n = some us → ∀ u ∈ us, U u := by
    intro n us hr u hu
    rcases rowOfG_mem hr u hu with h | h | h
    · exact hU _ h
    · exact hU' _ h
    · exact hU'' _ h
  rcases hs with ⟨rfl, rfl⟩ | ⟨f, f', rfl, rfl, hff⟩
  · simp only [listRowG, alignedAll_none] at h ⊢
    rw [e1, e2]
    cases hu : rowOfG pre₂ sp₂ suf₂ (fpre.length + fsuf.length) with
    | none => rfl
    | some us =>
      rw [hu] at h
      simp only at h ⊢
      exact anyZipG_mono (forall₂_append hp hf) (hrowU hu) h
  · cases sp₂ with
    | none =>
      simp only [listRowG, alignedAll_some_none] at h ⊢
      cases hf' : rowOfG fpre' (some f') fsuf' (pre₂.length + suf₂.length) with
      | none => rfl
      | some fs' =>
        have hs' := rowOfG_some_isSome fpre' f' fsuf' (pre₂.length + suf₂.length)
        rw [hf'] at hs'
        have hfit : fpre.length + fsuf.length ≤ pre₂.length + suf₂.length := by
          have := of_decide_eq_true hs'.symm
          omega
        obtain ⟨fs, hfs⟩ := rowOfG_total (pre := fpre) (suf := fsuf) (c := f) hfit
        rw [hfs] at h
        have hF := rowOfG_forall₂ (R := TestMono U) hp (Or.inr ⟨f, f', rfl, rfl, hff⟩) hf hfs hf'
        refine anyZipG_mono hF ?_ h
        intro u hu
        rcases List.mem_append.mp hu with hu | hu
        · exact hU u hu
        · exact hU'' u hu
    | some c =>
      simp only [listRowG, alignedAll_some_some] at h ⊢
      rw [e1, e2]
      refine List.all_eq_true.mpr fun n hn => ?_
      have hn' := List.all_eq_true.mp h n hn
      have hlo := (List.mem_range'_1.mp hn).1
      obtain ⟨fs, hfs⟩ := rowOfG_total (pre := fpre) (suf := fsuf) (c := f) (n := n)
        (Nat.le_trans (Nat.le_max_left _ _) hlo)
      obtain ⟨fs', hfs'⟩ := rowOfG_total (pre := fpre') (suf := fsuf') (c := f') (n := n)
        (by rw [e1, e2]; exact Nat.le_trans (Nat.le_max_left _ _) hlo)
      obtain ⟨us, hus⟩ := rowOfG_total (pre := pre₂) (suf := suf₂) (c := c) (n := n)
        (Nat.le_trans (Nat.le_max_right _ _) hlo)
      rw [hfs, hus] at hn'
      rw [hfs', hus]
      exact anyZipG_mono (rowOfG_forall₂ (R := TestMono U) hp (Or.inr ⟨f, f', rfl, rfl, hff⟩) hf hfs hfs')
        (hrowU hus) hn'

omit [Leaf B] in
/-- **The object row keeps its answer `true`** under tests that imply tests, at the arguments
    that the row reads. -/
theorem famObjG_mono {NR : Nat} {fs : Finset String} {md : {x // x ∈ fs} → SlotMode B}
    {g g' : {x // x ∈ fs} → Graph B NR → Bool} {mw mw' : Graph B NR → Bool}
    {U : Graph B NR → Prop} (hg : ∀ k, TestMono U (g k) (g' k)) (hmw : TestMono U mw mw')
    {fs' : Finset String} {md' : {x // x ∈ fs'} → SlotMode B} {s' : Fin 2}
    {b : (TOp.obj fs' md' s' (B := B)).Pos → Graph B NR}
    (hU : ∀ k : {x // x ∈ fs}, U (slotAtG (md := md') b k.1).2)
    (hU' : ∀ k : {x // x ∈ fs'}, U (b (.inl k)))
    (h : famObjG (md := md) g mw (.node (.obj fs' md' s') b) = true) :
    famObjG (md := md) g' mw' (.node (.obj fs' md' s') b) = true := by
  simp only [famObjG, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at h ⊢
  rcases h with ⟨k, hk, h1, h2⟩ | ⟨k, hk, ⟨h1, h2⟩, h3⟩
  · exact Or.inl ⟨k, hk, h1, hg k _ (hU k) h2⟩
  · exact Or.inr ⟨k, hk, ⟨h1, h2⟩, hmw _ (hU' k) h3⟩

end Mono

section RightC
variable {NR : Nat} (sR : Fin NR → Graph B NR)

omit [Leaf B] in
/-- **The right rows keep their answer `true`**, where the restarts at the entries of the term
    imply restarts, and the family implies a family at each flat term that satisfies `U`. A child
    of a term that keeps its positions satisfies `U` where the term does. -/
theorem rightC_mono_u (U : Graph B NR → Prop)
    (hU : ∀ (op : TOp B) (a : op.Pos → Graph B NR) (p : op.Pos), TOp.kind op ≠ .wall →
      U (.node op a) → U (a p))
    {restart restart' fam fam' : Graph B NR → Bool}
    (hf : ∀ y', Flat1 y' = true → U y' → fam y' = true → fam' y' = true) :
    ∀ y : Graph B NR, Flat1 y = true → U y →
      (∀ j, y.ulv (TSig B) j = true → restart (sR j) = true → restart' (sR j) = true) →
      rightC sR restart fam y = true → rightC sR restart' fam' y = true := by
  intro y
  induction y with
  | leaf j =>
    intro hy hu hr h
    simp only [rightC, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact Or.inl (hf _ hy hu h)
    · exact Or.inr (hr j (by simp [Flat.ulv]) h)
  | node op a ih =>
    intro hy hu hr h
    cases op with
    | never => rfl
    | refine q qA =>
      simp only [rightC, Bool.or_eq_true] at h ⊢
      rcases h with h | h
      · exact Or.inl (hf _ hy hu h)
      · exact Or.inr (ih () (flat1_keep rfl hy ()) (hU (TOp.refine q qA) a () (fun hk => nomatch hk) hu)
          (fun j hj => hr j (ulv_keep (o := TOp.refine q qA) rfl () hj)) h)
    | union m =>
      simp only [rightC, Bool.or_eq_true] at h ⊢
      rcases h with h | h
      · exact Or.inl (hf _ hy hu h)
      · refine Or.inr (List.all_eq_true.mpr fun p hp => ?_)
        exact ih p (flat1_keep rfl hy p) (hU (TOp.union m) a p (fun hk => nomatch hk) hu)
          (fun j hj => hr j (ulv_keep (o := TOp.union m) rfl p hj)) (List.all_eq_true.mp h p hp)
    | prim g => exact hf _ hy hu h
    | set => exact hf _ hy hu h
    | list _ _ _ => exact hf _ hy hu h
    | obj _ _ _ => exact hf _ hy hu h
    | opaq => exact hf _ hy hu h
    | held _ _ _ => exact hf _ hy hu h
    | legacy _ => exact hf _ hy hu h

omit [Leaf B] in
/-- **The right rows keep their answer `true`** at the flat terms. -/
theorem rightC_mono {restart restart' fam fam' : Graph B NR → Bool}
    (hf : ∀ y', Flat1 y' = true → fam y' = true → fam' y' = true) :
    ∀ y : Graph B NR, Flat1 y = true →
      (∀ j, y.ulv (TSig B) j = true → restart (sR j) = true → restart' (sR j) = true) →
      rightC sR restart fam y = true → rightC sR restart' fam' y = true :=
  fun y hy hr h => rightC_mono_u sR (fun _ => True) (fun _ _ _ _ _ => trivial)
    (fun y' h1 _ h2 => hf y' h1 h2) y hy trivial hr h

end RightC

section Measure
variable {NL NR : Nat} (sL : Fin NL → Graph B NL) (sR : Fin NR → Graph B NR)
  (ρL : Fin NL → Nat) (ρR : Fin NR → Nat)

/-- **The ranks of two flat systems**: each unguarded edge lowers the rank, a rank is below the
    count of entries, and each entry is a flat term. -/
structure Fueled : Prop where
  ltL : ∀ i, ρL i < NL
  ltR : ∀ j, ρR j < NR
  edgeL : ∀ i j, (sL i).ulv (TSig B) j = true → ρL j < ρL i
  edgeR : ∀ i j, (sR i).ulv (TSig B) j = true → ρR j < ρR i
  flatL : ∀ i, Flat1 (sL i) = true
  flatR : ∀ j, Flat1 (sR j) = true

/-- Every pair of an entry of the left operand and an entry of the right operand. -/
def allPairs (NL NR : Nat) : List (Fin NL × Fin NR) :=
  (List.finRange NL).flatMap fun i => (List.finRange NR).map fun j => (i, j)

/-- Each pair of entries is a member of the pairs. -/
theorem mem_allPairs {NL NR : Nat} (i : Fin NL) (j : Fin NR) : (i, j) ∈ allPairs NL NR := by
  simp only [allPairs, List.mem_flatMap, List.mem_map]
  exact ⟨i, List.mem_finRange i, j, List.mem_finRange j, rfl⟩

/-- Whether a table holds the pair of an entry of each operand. -/
def holds {NL NR : Nat} (A : Tbl NL NR) (p : Fin NL × Fin NR) : Bool :=
  A.any fun q => decide (q.1 = p.1) && decide (q.2 = p.2)

/-- The pairs of entries that a table lacks. -/
def freeCnt {NL NR : Nat} (A : Tbl NL NR) : Nat :=
  ((allPairs NL NR).filter fun p => !holds A p).length

/-- **A new pair of entries lowers the count of the pairs that the table lacks.** -/
theorem freeCnt_cons_lt {NL NR : Nat} {A : Tbl NL NR} {i : Fin NL} {j : Fin NR}
    (h : A.any (fun q => decide (q.1 = i) && decide (q.2 = j)) = false) :
    freeCnt ((i, j) :: A) < freeCnt A := by
  have hpred : ∀ p : Fin NL × Fin NR, (!holds ((i, j) :: A) p) =
      (!(decide (i = p.1) && decide (j = p.2)) && !holds A p) := by
    intro p
    simp only [holds, List.any_cons, Bool.not_or]
  unfold freeCnt
  rw [List.filter_congr (fun p _ => hpred p), ← List.filter_filter]
  have hm : (i, j) ∈ List.filter (fun p => !holds A p) (allPairs NL NR) := by
    refine List.mem_filter.mpr ⟨mem_allPairs i j, ?_⟩
    simp only [holds, h]; rfl
  exact (List.length_filter_lt_length_iff_exists
    (p := fun a => !(decide (i = a.1) && decide (j = a.2)))).mpr ⟨(i, j), hm, by simp⟩

/-- **The budget of a table**: the pairs of entries that the table lacks, each worth the unguarded
    steps between two guards, and a reserve for a pair against the bottom. -/
def budget (NL NR : Nat) (A : Tbl NL NR) : Nat := freeCnt A * (NL + NR) + NL

omit [Leaf B] in
/-- **The measure of a call.** -/
def phi (A : Tbl NL NR) (x : Graph B NL) (y : Graph B NR) : Nat :=
  budget NL NR A + hgt ρL x + hgt ρR y

omit [Leaf B] in
/-- **A new pair of entries lowers the measure below the budget of the table.** -/
theorem push_lt (F : Fueled sL sR ρL ρR) {A : Tbl NL NR} {i : Fin NL} {j : Fin NR}
    (hA : A.any (fun q => decide (q.1 = i) && decide (q.2 = j)) = false) :
    phi ρL ρR ((i, j) :: A) (sL i) (sR j) < budget NL NR A := by
  have hf := freeCnt_cons_lt hA
  have h1 := hgt_entry (B := B) (sys := sL) F.edgeL i
  have h2 := hgt_entry (B := B) (sys := sR) F.edgeR j
  have h3 := F.ltL i
  have h4 := F.ltR j
  have h5 := Nat.mul_le_mul_right (NL + NR) (Nat.succ_le_of_lt hf)
  rw [Nat.succ_mul] at h5
  unfold phi budget
  omega

omit [Leaf B] in
/-- The arguments of a test: an entry, or the bottom. -/
def LeafOrNever {N : Nat} (u : Graph B N) : Prop :=
  (∃ j, u = .leaf j) ∨ ∃ a', u = .node .never a'

/-- **A call that the measure bounds**: the walk `prev` answering `true` makes the walk `prev'`
    answer `true`, at the terms that satisfy the invariants `PL` and `PR`. -/
def MonoAtP (PL : Graph B NL → Prop) (PR : Graph B NR → Prop)
    (prev prev' : Tbl NL NR → Graph B NL → Graph B NR → Bool) (m : Nat) : Prop :=
  ∀ A x y, PL x → PR y → phi ρL ρR A x y < m → prev A x y = true → prev' A x y = true

/-- **A call that the measure bounds**, at the flat terms. -/
def MonoAt (prev prev' : Tbl NL NR → Graph B NL → Graph B NR → Bool) (m : Nat) : Prop :=
  MonoAtP ρL ρR (fun t => Flat1 t = true) (fun t => Flat1 t = true) prev prev' m

omit [Leaf B] in
/-- **The walk answers `true` against the bottom** at every term below the count of entries. -/
def NeverAt (prev' : Tbl NL NR → Graph B NL → Graph B NR → Bool) : Prop :=
  ∀ A x a', hgt ρL x < NL → prev' A x (.node .never a') = true

omit [Leaf B] in
/-- **A pair below a guard keeps its answer `true`**, where the test `self` of the row keeps its
    answer against the bottom. -/
theorem pairX_mono_gen (F : Fueled sL sR ρL ρR) {PL : Graph B NL → Prop} {PR : Graph B NR → Prop}
    (hPL : ∀ i, PL (sL i)) (hPR : ∀ j, PR (sR j))
    {prev prev' : Tbl NL NR → Graph B NL → Graph B NR → Bool} {m : Nat}
    (hM : MonoAtP ρL ρR PL PR prev prev' m) {A : Tbl NL NR} (hm : budget NL NR A ≤ m) (i : Fin NL)
    (u : Graph B NR) (hu : LeafOrNever u) (self self' : Graph B NR → Bool)
    (hs : ∀ a', self' (.node .never a') = true) :
    pairX (sL := sL) (sR := sR) prev A (.leaf i) self u = true →
      pairX (sL := sL) (sR := sR) prev' A (.leaf i) self' u = true := by
  rcases hu with ⟨j, rfl⟩ | ⟨a', rfl⟩
  · intro h
    simp only [pairX, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact Or.inl h
    · cases hany : A.any (fun p => decide (p.1 = i) && decide (p.2 = j))
      · exact Or.inr (hM ((i, j) :: A) (sL i) (sR j) (hPL i) (hPR j)
          (Nat.lt_of_lt_of_le (push_lt sL sR ρL ρR F hany) hm) h)
      · exact Or.inl rfl
  · intro _
    exact hs a'

/-- **A pair below a guard keeps its answer `true`.** -/
theorem pairX_mono (F : Fueled sL sR ρL ρR) {prev prev' : Tbl NL NR → Graph B NL → Graph B NR → Bool}
    {m : Nat} (hM : MonoAt ρL ρR prev prev' m) (hN : NeverAt ρL prev') {A : Tbl NL NR}
    (hm : budget NL NR A ≤ m) (i : Fin NL) (u : Graph B NR)
    (hu : LeafOrNever u) :
    pairX (sL := sL) (sR := sR) prev A (.leaf i) (rowG sL sR prev A (.leaf i)) u = true →
      pairX (sL := sL) (sR := sR) prev' A (.leaf i) (rowG sL sR prev' A (.leaf i)) u = true :=
  pairX_mono_gen sL sR ρL ρR F F.flatL F.flatR hM hm i u hu _ _
    (fun a' => hN A (sL i) a' (Nat.lt_of_le_of_lt (hgt_entry (B := B) (sys := sL) F.edgeL i) (F.ltL i)))

end Measure

section RowMono

omit [Leaf B] in
/-- A member of the parts of a list node is a position of the node. -/
theorem listParts_mem {N n m : Nat} {s : Fin 2}
    (a : (TOp.list n s m (B := B)).Pos → Graph B N) {t : Graph B N}
    (h : t ∈ (listParts a).1 ∨ (listParts a).2.1 = some t ∨ t ∈ (listParts a).2.2) :
    ∃ q, a q = t := by
  rcases h with h | h | h
  · obtain ⟨p, rfl⟩ := List.mem_ofFn.mp h
    exact ⟨_, rfl⟩
  · obtain ⟨p, hp⟩ := optOf_mem s (fun p => a (.inr (.inl p))) t (by simpa [listParts] using h)
    exact ⟨_, hp⟩
  · obtain ⟨p, rfl⟩ := List.mem_ofFn.mp h
    exact ⟨_, rfl⟩

omit [Leaf B] in
/-- Two tests of a position, one implying the other, give two tests of a list of positions. -/
theorem forall₂_map_map {X Y : Type} {R : Y → Y → Prop} {l : List X} {f g : X → Y}
    (h : ∀ t ∈ l, R (f t) (g t)) : List.Forall₂ R (l.map f) (l.map g) := by
  induction l with
  | nil => exact .nil
  | cons t l ih =>
    exact .cons (h t List.mem_cons_self) (ih fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))

omit [Leaf B] in
/-- The block test of an object keeps its answer `true` under tests that imply tests. -/
theorem blockX_mono {NR : Nat} {fs : Finset String} {md : {x // x ∈ fs} → SlotMode B}
    {U : Graph B NR → Prop} (w : Fin 2)
    (g g' : (TOp.obj fs md w (B := B)).Pos → Graph B NR → Bool)
    (h : ∀ q, TestMono U (g q) (g' q)) :
    TestMono U (blockX (md := md) w g) (blockX (md := md) w g') := by
  match w, g, g', h with
  | ⟨0, _⟩, _, _, _ => exact fun _ _ h => h
  | ⟨1, _⟩, g, g', h => exact h _

omit [Leaf B] in
/-- **The slot of a name in an object of flat terms is an entry or the bottom.** -/
theorem slotAtG_leafOrNever {NR : Nat} {fs : Finset String} {md : {x // x ∈ fs} → SlotMode B}
    {w : Fin 2} {b : (TOp.obj fs md w (B := B)).Pos → Graph B NR}
    (hb : ∀ q, ∃ j, b q = .leaf j) (n : String) : LeafOrNever (slotAtG (md := md) b n).2 := by
  unfold slotAtG
  split
  · obtain ⟨j, hj⟩ := hb (.inl ⟨n, ‹_›⟩); exact Or.inl ⟨j, hj⟩
  · match w, b, hb with
    | ⟨0, _⟩, _, _ => exact Or.inr ⟨(fun p => nomatch p), rfl⟩
    | ⟨1, _⟩, b, hb => obtain ⟨j, hj⟩ := hb (.inr ⟨0, Nat.one_pos⟩); exact Or.inl ⟨j, hj⟩

end RowMono

section RowMonoMain
variable {NL NR : Nat} (sL : Fin NL → Graph B NL) (sR : Fin NR → Graph B NR)
  (ρL : Fin NL → Nat) (ρR : Fin NR → Nat)

/-- **A row keeps its answer `true`** where the walk that it reads does, at the calls that the
    measure bounds. -/
theorem row_mono (F : Fueled sL sR ρL ρR)
    {prev prev' : Tbl NL NR → Graph B NL → Graph B NR → Bool} {m : Nat}
    (hM : MonoAt ρL ρR prev prev' m) (hN : NeverAt ρL prev') (A : Tbl NL NR) :
    ∀ x : Graph B NL, Flat1 x = true → ∀ y : Graph B NR, Flat1 y = true →
      phi ρL ρR A x y ≤ m →
      rowG sL sR prev A x y = true → rowG sL sR prev' A x y = true := by
  intro x
  induction x with
  | leaf j =>
    intro hx y hy hφ h
    have h1 := le_hgt_leaf (B := B) ρL j
    have h2 := hgt_entry (B := B) (sys := sL) F.edgeL j
    refine hM A (sL j) y (F.flatL j) hy ?_ h
    unfold phi at hφ ⊢
    omega
  | node op a ih =>
    intro hx y hy hφ h
    have hbud : budget NL NR A ≤ m := by unfold phi at hφ; omega
    have hr : ∀ j, y.ulv (TSig B) j = true → prev A (.node op a) (sR j) = true →
        prev' A (.node op a) (sR j) = true := by
      intro j hj hp
      have h1 := le_hgt (ρ := ρR) hj
      have h2 := hgt_entry (B := B) (sys := sR) F.edgeR j
      refine hM A _ (sR j) hx (F.flatR j) ?_ hp
      unfold phi at hφ ⊢
      omega
    cases op with
    | never => rfl
    | refine q qA =>
      simp_rowG at h ⊢
      refine ih () (flat1_keep rfl hx ()) y hy ?_ h
      have := hgt_child ρL a (o := TOp.refine q qA) rfl ()
      unfold phi at hφ ⊢
      omega
    | union k =>
      simp_rowG at h ⊢
      refine List.all_eq_true.mpr fun p hp => ?_
      refine ih p (flat1_keep rfl hx p) y hy ?_ (List.all_eq_true.mp h p hp)
      have := hgt_child ρL a (o := TOp.union k) rfl p
      unfold phi at hφ ⊢
      omega
    | prim g =>
      simp_rowG at h ⊢
      exact rightC_mono sR (fun y' _ h' => h') y hy hr h
    | opaq =>
      simp_rowG at h ⊢
      exact rightC_mono sR (fun y' _ h' => h') y hy hr h
    | held _ _ _ =>
      simp_rowG at h ⊢
      exact rightC_mono sR (fun y' _ h' => h') y hy hr h
    | legacy _ =>
      simp_rowG at h ⊢
      exact rightC_mono sR (fun y' _ h' => h') y hy hr h
    | set =>
      obtain ⟨i, hi⟩ := flat1_down (o := TOp.set) rfl hx ()
      simp_rowG at h ⊢
      rw [hi] at h ⊢
      refine rightC_mono sR ?_ y hy hr h
      intro y' hy' hfam
      cases y' with
      | leaf _ => exact nomatch hfam
      | node op' b =>
        cases op' with
        | set =>
          obtain ⟨j, hj⟩ := flat1_down (o := TOp.set) rfl hy' ()
          simp only [famSetG] at hfam ⊢
          exact pairX_mono sL sR ρL ρR F hM hN hbud i _ (Or.inl ⟨j, hj⟩) hfam
        | prim _ => exact hfam
        | list _ _ _ => exact hfam
        | obj _ _ _ => exact hfam
        | _ => exact nomatch hfam
    | list n s k =>
      have hdown := fun q => flat1_down (o := TOp.list n s k) rfl hx q
      simp_rowG at h ⊢
      rw [listPartsX_eq a (fun x => pairX (sL := sL) (sR := sR) prev A x (rowG sL sR prev A x))] at h
      rw [listPartsX_eq a (fun x => pairX (sL := sL) (sR := sR) prev' A x (rowG sL sR prev' A x))]
      refine rightC_mono sR ?_ y hy hr h
      intro y' hy' hfam
      cases y' with
      | leaf _ => exact nomatch hfam
      | node op' b =>
        cases op' with
        | list n' s' k' =>
          have hbd := fun q => flat1_down (o := TOp.list n' s' k') rfl hy' q
          have hU : ∀ t, (t ∈ (listParts b).1 ∨ (listParts b).2.1 = some t ∨ t ∈ (listParts b).2.2) →
              LeafOrNever t := by
            intro t ht
            obtain ⟨q, rfl⟩ := listParts_mem b ht
            obtain ⟨j, hj⟩ := hbd q
            exact Or.inl ⟨j, hj⟩
          have hT : ∀ t, (t ∈ (listParts a).1 ∨ (listParts a).2.1 = some t ∨ t ∈ (listParts a).2.2) →
              TestMono LeafOrNever
                ((fun x => pairX (sL := sL) (sR := sR) prev A x (rowG sL sR prev A x)) t)
                ((fun x => pairX (sL := sL) (sR := sR) prev' A x (rowG sL sR prev' A x)) t) := by
            intro t ht
            obtain ⟨q, rfl⟩ := listParts_mem a ht
            obtain ⟨i, hi⟩ := hdown q
            rw [hi]
            exact fun u hu h => pairX_mono sL sR ρL ρR F hM hN hbud i u hu h
          simp only [famListG] at hfam ⊢
          refine listRowG_mono (U := LeafOrNever) (forall₂_map_map fun t ht => hT t (Or.inl ht)) ?_
            (forall₂_map_map fun t ht => hT t (Or.inr (Or.inr ht)))
            (fun u hu => hU u (Or.inl hu)) (fun u hu => hU u (Or.inr (Or.inl hu)))
            (fun u hu => hU u (Or.inr (Or.inr hu))) hfam
          cases hsp : (listParts a).2.1 with
          | none => exact Or.inl ⟨rfl, rfl⟩
          | some t => exact Or.inr ⟨_, _, rfl, rfl, hT t (Or.inr (Or.inl hsp))⟩
        | prim _ => exact hfam
        | set => exact hfam
        | obj _ _ _ => exact hfam
        | _ => exact nomatch hfam
    | obj fs md w =>
      have hdown := fun q => flat1_down (o := TOp.obj fs md w) rfl hx q
      simp_rowG at h ⊢
      refine rightC_mono sR ?_ y hy hr h
      intro y' hy' hfam
      cases y' with
      | leaf _ => exact nomatch hfam
      | node op' b =>
        cases op' with
        | obj fs' md' w' =>
          have hbd := fun q => flat1_down (o := TOp.obj fs' md' w') rfl hy' q
          have hT : ∀ q, TestMono LeafOrNever
              ((fun x => pairX (sL := sL) (sR := sR) prev A x (rowG sL sR prev A x)) (a q))
              ((fun x => pairX (sL := sL) (sR := sR) prev' A x (rowG sL sR prev' A x)) (a q)) := by
            intro q
            obtain ⟨i, hi⟩ := hdown q
            rw [hi]
            exact fun u hu h => pairX_mono sL sR ρL ρR F hM hN hbud i u hu h
          exact famObjG_mono (md := md) (fun k => hT (.inl k)) (blockX_mono w _ _ hT)
            (fun k => slotAtG_leafOrNever hbd k.1)
            (fun k => by obtain ⟨j, hj⟩ := hbd (.inl k); exact Or.inl ⟨j, hj⟩) hfam
        | prim _ => exact hfam
        | set => exact hfam
        | list _ _ _ => exact hfam
        | _ => exact nomatch hfam

end RowMonoMain

section Adequacy
variable {NL NR : Nat} (sL : Fin NL → Graph B NL) (sR : Fin NR → Graph B NR)
  (ρL : Fin NL → Nat) (ρR : Fin NR → Nat)

section Generic
variable {sL sR}

/-- **The hypothesis on a row, one**: the row keeps its answer `true` from a walk to a walk at the
    calls that the measure bounds, at the terms that satisfy the invariants. -/
def RowMono (PL : Graph B NL → Prop) (PR : Graph B NR → Prop) (R : Row sL sR) : Prop :=
  ∀ (prev prev' : Tbl NL NR → Graph B NL → Graph B NR → Bool) (m : Nat),
    MonoAtP ρL ρR PL PR prev prev' m → NeverAt ρL prev' → ∀ A x y, PL x → PR y →
      phi ρL ρR A x y ≤ m → goW R prev A x y = true → goW R prev' A x y = true

omit [Leaf B] in
/-- **The hypothesis on a row, two**: the row answers `true` against the bottom where the walk does
    at the terms below the fuel. -/
def RowNever (R : Row sL sR) : Prop :=
  ∀ (prev : Tbl NL NR → Graph B NL → Graph B NR → Bool) (n : Nat),
    (∀ A x a', hgt ρL x < n → prev A x (.node .never a') = true) →
      ∀ A x a', hgt ρL x < n + 1 → goW R prev A x (.node .never a') = true

variable {ρL ρR}

omit [Leaf B] in
/-- **A walk answers `true` against the bottom** at each term below the fuel. -/
theorem walk_never {R : Row sL sR} (hN : RowNever ρL R) :
    ∀ (n : Nat) (A : Tbl NL NR) (x : Graph B NL) (a' : (TSig B).Pos TOp.never → Graph B NR),
      hgt ρL x < n → walk R n A x (.node .never a') = true
  | 0 => fun _ _ _ h => absurd h (Nat.not_lt_zero _)
  | n + 1 => fun A x a' h => hN (walk R n) n (fun A x a' h' => walk_never hN n A x a' h') A x a' h

omit [Leaf B] in
/-- **Generic adequacy**: where the optimistic walk answers `true`, so does the walk at each fuel
    above the measure of the call. -/
theorem walkO_imp_walk {PL : Graph B NL → Prop} {PR : Graph B NR → Prop} {R : Row sL sR}
    (F : Fueled sL sR ρL ρR) (hM : RowMono ρL ρR PL PR R) (hN : RowNever ρL R) :
    ∀ (n : Nat) (A : Tbl NL NR) (x : Graph B NL) (y : Graph B NR), PL x → PR y →
      phi ρL ρR A x y < n → walkO R n A x y = true → walk R n A x y = true
  | 0 => fun A x y _ _ h => absurd h (Nat.not_lt_zero _)
  | n + 1 => fun A x y hx hy hφ h => by
    have hn : NL ≤ n := by unfold phi budget at hφ; omega
    exact hM (walkO R n) (walk R n) n
      (fun A x y hx hy hlt => walkO_imp_walk F hM hN n A x y hx hy hlt)
      (fun A x a' hlt => walk_never hN n A x a' (by omega)) A x y hx hy (by omega) h

end Generic

omit [Leaf B] in
/-- The unguarded height of an entry is at most its rank plus one. -/
theorem hgt_leaf_le {N : Nat} (ρ : Fin N → Nat) (j : Fin N) : hgt ρ (.leaf j : Graph B N) ≤ ρ j + 1 :=
  hgt_le fun k hk => by
    have : j = k := by simpa [Flat.ulv] using hk
    subst this; exact Nat.le_refl _

/-- The pairs of entries number the product of the two counts of entries. -/
theorem length_allPairs (NL NR : Nat) : (allPairs NL NR).length = NL * NR := by
  simp [allPairs, List.length_flatMap]

omit [Leaf B] in
/-- **The measure of the first call is below the fuel.** -/
theorem phi_root_lt (F : Fueled sL sR ρL ρR) (rL : Fin NL) (rR : Fin NR) :
    phi ρL ρR [] (.leaf rL : Graph B NL) (.leaf rR : Graph B NR) < fuel NL NR := by
  have h1 := hgt_leaf_le (B := B) ρL rL
  have h2 := hgt_leaf_le (B := B) ρR rR
  have h3 := F.ltL rL
  have h4 := F.ltR rR
  have hf : freeCnt ([] : Tbl NL NR) ≤ NL * NR := by
    unfold freeCnt
    rw [← length_allPairs NL NR]
    exact List.length_filter_le _ _
  have hNR : 1 ≤ NR := by omega
  have h5 := Nat.mul_le_mul_right (NL + NR) hf
  have h6 : NL ≤ NL * NR := by simpa using Nat.mul_le_mul_left NL hNR
  unfold phi budget fuel
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul] at *
  omega

omit [Leaf B] in
/-- **The fuel of the root call is adequate**, for each row that satisfies the two hypotheses. -/
theorem walkO_fuel_imp_walk {PL : Graph B NL → Prop} {PR : Graph B NR → Prop} {R : Row sL sR}
    (F : Fueled sL sR ρL ρR) (hM : RowMono ρL ρR PL PR R) (hN : RowNever ρL R) (rL : Fin NL)
    (rR : Fin NR) (hL : PL (.leaf rL)) (hR : PR (.leaf rR))
    (h : walkO R (fuel NL NR) [] (.leaf rL) (.leaf rR) = true) :
    walk R (fuel NL NR) [] (.leaf rL) (.leaf rR) = true :=
  walkO_imp_walk F hM hN _ _ _ _ hL hR (phi_root_lt sL sR ρL ρR F rL rR) h

/-- **The row of disjointness keeps its answer `true`** at the flat terms. -/
theorem rowMono_G (F : Fueled sL sR ρL ρR) :
    RowMono ρL ρR (fun t => Flat1 t = true) (fun t => Flat1 t = true) (rowSpecG sL sR) :=
  fun _ _ _ hM hN A x y hx hy hφ h => row_mono sL sR ρL ρR F hM hN A x hx y hy hφ h

/-- **The row of disjointness answers `true` against the bottom.** -/
theorem rowNever_G (hρ : ∀ i j, (sL i).ulv (TSig B) j = true → ρL j < ρL i) :
    RowNever ρL (rowSpecG sL sR) :=
  fun prev n hprev A x a' h => rowG_right_never sL sR hρ prev n hprev A x a' h

/-- **The fuel of `disjoint` is adequate**: where the optimistic walk answers `true`, so does the
    walk. -/
theorem decO_fuel_imp_decG (F : Fueled sL sR ρL ρR) (rL : Fin NL) (rR : Fin NR)
    (h : decO sL sR (fuel NL NR) [] (.leaf rL) (.leaf rR) = true) :
    decG sL sR (fuel NL NR) [] (.leaf rL) (.leaf rR) = true :=
  walkO_fuel_imp_walk sL sR ρL ρR F (rowMono_G sL sR ρL ρR F) (rowNever_G sL sR ρL F.edgeL) rL rR rfl rfl h

end Adequacy

section Closed
variable {N : Nat}

omit [Leaf B] in
/-- **The inlining of a stratified term is flat**, where each leaf for an entry that a container
    holds names an entry. -/
theorem flat1_inl {w k : Nat} (σw : Fin w → Graph B N) (σk : Fin k → Graph B N)
    (hw : ∀ j, ∃ l, σw j = .leaf l) (hk : ∀ j, Flat1 (σk j) = true) :
    ∀ t : Term B w k, Flat1 (t.inl σw σk) = true := by
  intro t
  induction t with
  | leaf j => exact hk j
  | node o h args ih =>
    unfold SFlat.inl Flat1
    simp only [h]
    exact List.all_eq_true.mpr fun p _ => ih p.1
  | down o h args =>
    unfold SFlat.inl Flat1
    simp only [h]
    refine List.all_eq_true.mpr fun p _ => ?_
    obtain ⟨l, hl⟩ := hw (args p)
    simp only [hl]
  | wall o h args =>
    unfold SFlat.inl Flat1
    simp only [h]

omit [Leaf B] in
/-- **Each entry of the graph of a closed codec is a flat term.** -/
theorem flat1_graph (d : Closed B N) (i : Fin N) : Flat1 (d.graph i) = true :=
  flat1_inl _ _ (fun j => ⟨j, rfl⟩) (fun _ => rfl) (d i)

omit [Leaf B] in
/-- **The graphs of two closed codecs are fueled**, at the index of each entry as the rank. -/
theorem Closed.fueled {NL NR : Nat} (dL : Closed B NL) (dR : Closed B NR) :
    Fueled dL.graph dR.graph (fun i => i.val) (fun j => j.val) where
  ltL i := i.isLt
  ltR j := j.isLt
  edgeL i j h := (SSys.order dL).1 i j h
  edgeR i j h := (SSys.order dR).1 i j h
  flatL i := flat1_graph dL i
  flatR j := flat1_graph dR j

end Closed

end Fuel

end Calculus.Alg.Scoped
