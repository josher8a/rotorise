import Calculus.Lang.ScopeFuel

/-!
# The decision is exact over the fragment

`Scoped.disjoint_sound` proves that the answer `true` is correct. This module proves the converse
over the fragment of free constructors: where `disjoint` answers `false`, the two meanings share a
datum (`disjoint_exact`). The universe supplies the dual of its laws (`WLaws`): two primitives that
the leaf does not keep apart share a datum, and so do two sets over elements that share one.

`decO_complete` is the core: over the fragment, the walk whose empty fuel answers `true` answers
`false` only where the two terms share a datum. The proof is an induction on the fuel and then on
the left term, with one case for each former. A list builds the datum at one common length from
the row, an object builds a map from the names that one side requires, and a set builds a one
element set from the datum of the elements. `decO_fuel_imp_decG` closes the gap to `disjoint`: the
fuel of `disjoint` is enough for the walk that reads an empty fuel as `true`.
-/

namespace Calculus.Alg.Scoped

/-- A list that fails `all` has a member that fails. -/
theorem all_false' {X : Type} {f : X → Bool} : ∀ {l : List X}, l.all f = false → ∃ x ∈ l, f x = false
  | [], h => nomatch h
  | x :: xs, h => by
    cases hx : f x
    · exact ⟨x, List.mem_cons_self, hx⟩
    · rw [List.all_cons, hx, Bool.true_and] at h
      obtain ⟨y, hy, hfy⟩ := all_false' h
      exact ⟨y, List.mem_cons_of_mem _ hy, hfy⟩

section RowsFalse

/-- **A failed zip tests each aligned position as `false`.** -/
theorem anyZipG_false {X : Type} : ∀ {fs : List (X → Bool)} {us : List X},
    fs.length = us.length → anyZipG fs us = false → List.Forall₂ (fun f u => f u = false) fs us
  | [], [], _, _ => .nil
  | [], _ :: _, h, _ => nomatch h
  | _ :: _, [], h, _ => nomatch h
  | f :: fs, u :: us, h, hz => by
    simp only [anyZipG, Bool.or_eq_false_iff] at hz
    exact .cons hz.1 (anyZipG_false (by simpa using h) hz.2)

/-- **Where the list row answers `false`**, some common length has two rows with no disjoint
    position. -/
theorem listRowG_false {X : Type} {fpre fsuf : List (X → Bool)} {fsp : Option (X → Bool)}
    {pre₂ suf₂ : List X} {sp₂ : Option X}
    (h : listRowG fpre fsp fsuf pre₂ sp₂ suf₂ = false) :
    ∃ n fs us, rowOfG fpre fsp fsuf n = some fs ∧ rowOfG pre₂ sp₂ suf₂ n = some us ∧
      anyZipG fs us = false := by
  cases fsp with
  | none =>
    simp only [listRowG, alignedAll_none] at h
    cases hu : rowOfG pre₂ sp₂ suf₂ (fpre.length + fsuf.length) with
    | none => rw [hu] at h; exact nomatch h
    | some us =>
      rw [hu] at h
      exact ⟨_, fpre ++ fsuf, us, by rw [rowOfG_none_eq, if_pos rfl], hu, h⟩
  | some f =>
    cases sp₂ with
    | none =>
      simp only [listRowG, alignedAll_some_none] at h
      cases hf : rowOfG fpre (some f) fsuf (pre₂.length + suf₂.length) with
      | none => rw [hf] at h; exact nomatch h
      | some fs =>
        rw [hf] at h
        exact ⟨_, fs, pre₂ ++ suf₂, hf, by rw [rowOfG_none_eq, if_pos rfl], h⟩
    | some c =>
      simp only [listRowG, alignedAll_some_some] at h
      obtain ⟨n, hn, hm⟩ := all_false' h
      have hn' := List.mem_range'_1.mp hn
      obtain ⟨fs, hfs⟩ := rowOfG_total (pre := fpre) (suf := fsuf) (c := f) (n := n) (by omega)
      obtain ⟨us, hus⟩ := rowOfG_total (pre := pre₂) (suf := suf₂) (c := c) (n := n) (by omega)
      rw [hfs, hus] at hm
      exact ⟨n, fs, us, hfs, hus, hm⟩

end RowsFalse

section Frag
variable {S : Syn} [Sem S] [Leaf S.sig]

/-- A set element of the fragment: a union of primitives, which the universe holds in a set. -/
def elemFrag {N : Nat} (setOk : S.sig.Ground → Bool) : Graph S.sig N → Bool
  | .node (.prim g) _ => setOk g
  | .node (.union m) a => (List.finRange m).all fun p => elemFrag setOk (a p)
  | _ => false

/-- **The fragment**: the free constructors of the datum algebra. It has no predicate, no caller
    code, no top, and only the formers that the universe has. -/
def Frag {N : Nat} (setOk : S.sig.Ground → Bool) : Graph S.sig N → Bool
  | .leaf _ => true
  | .node (.prim _) _ | .node .never _ => true
  | .node (.union m) a => (List.finRange m).all fun p => Frag setOk (a p)
  | .node (.list x s y) a => (Mean.list (B := S.sig)).isSome &&
      (TOp.pos (B := S.sig) (.list x s y)).attach.all fun p => Frag setOk (a p.1)
  | .node (.obj fs md s) a => (Mean.map (B := S.sig)).isSome &&
      !(TOp.adapts (B := S.sig) (.obj fs md s)) &&
      (TOp.pos (B := S.sig) (.obj fs md s)).attach.all fun p => Frag setOk (a p.1)
  | .node .set a => (Mean.set (B := S.sig)).isSome && elemFrag setOk (a ())
  | _ => false

/-- **A codec that a set holds as an element**: a primitive that the universe holds in a set, or
    a union of such codecs. -/
inductive SetEl (setOk : S.sig.Ground → Bool) : Mean.C S.sig → Prop
  | ground (g : S.sig.Ground) : setOk g = true → SetEl setOk (Mean.ground g)
  | alt (cs : List (Mean.C S.sig)) (μ : Option (Mean.Mem (B := S.sig))) :
      (∀ c ∈ cs, SetEl setOk c) → SetEl setOk (altCodec cs μ)

omit [Leaf S.sig] in
/-- **A property of the elements that a set holds**, from its primitives and its unions. -/
theorem SetEl.rec' {setOk : S.sig.Ground → Bool} (P : Mean.C S.sig → Prop)
    (hg : ∀ g, setOk g = true → P (Mean.ground g))
    (ha : ∀ cs μ, (∀ c ∈ cs, P c) → P (altCodec cs μ)) {c : Mean.C S.sig}
    (h : SetEl setOk c) : P c := by
  induction h with
  | ground g hg' => exact hg g hg'
  | alt cs μ _ ih => exact ha cs μ ih

variable (S) (o : Orient) (setOk : S.sig.Ground → Bool)

/-- **The witness laws**, the dual of `Laws`: the primitive law and the set law. -/
structure WLaws : Prop where
  /-- Two primitives that the leaf does not keep apart share a datum. -/
  prim : ∀ g g' : S.sig.Ground, Leaf.primsApart g g' = false →
    ∃ v, ((Mean.ground (B := S.sig) g).f o v).isSome = true ∧
      ((Mean.ground (B := S.sig) g').f o v).isSome = true
  /-- Two sets over elements that share a datum share a set. -/
  set : ∀ L, Mean.set (B := S.sig) = some L → ∀ c c' : Mean.C S.sig,
    SetEl setOk c → SetEl setOk c' →
    (∃ u, (c.f o u).isSome = true ∧ (c'.f o u).isSome = true) →
    ∃ v, ((L.lift c).f o v).isSome = true ∧ ((L.lift c').f o v).isSome = true

end Frag

section Wit
variable {S : Syn} [Sem S] [Leaf S.sig] {τ : (s : Bool) → TableAt S.sig s} {o : Orient}
  {setOk : S.sig.Ground → Bool}

/-- **Two terms share a datum**: one datum is accepted by the meanings of both. -/
def Wit {NL NR : Nat} (dL : GSys τ NL) (dR : GSys τ NR) (o : Orient) (x : Graph S.sig NL)
    (y : Graph S.sig NR) : Prop :=
  ∃ v, ((mng τ dL x).f o v).isSome = true ∧ ((mng τ dR y).f o v).isSome = true

/-- The terms that a family reads: a primitive and the three formers. -/
def isFormer {N : Nat} : Graph S.sig N → Bool
  | .node (.prim _) _ | .node .set _ | .node (.list _ _ _) _ | .node (.obj _ _ _) _ => true
  | _ => false

/-- A list that fails `all` has a member that fails. -/
theorem all_false {X : Type} {f : X → Bool} {l : List X} (h : l.all f = false) :
    ∃ x ∈ l, f x = false := all_false' h

omit [Leaf S.sig] in
/-- A union accepts what one option accepts. -/
theorem union_of {N : Nat} (d : GSys τ N) {m : Nat} {a : Fin m → Graph S.sig N} (p : Fin m)
    {v : Mean.V (B := S.sig)} (h : ((mng τ d (a p)).f o v).isSome = true) :
    ((mng τ d (.node (.union m) a)).f o v).isSome = true :=
  (select_isSome_attempt _ _ _).mpr ⟨_, List.mem_ofFn.mpr ⟨p, rfl⟩, h⟩

omit [Leaf S.sig] in
/-- **The rows that read the right operand alone are complete**: where `rightC` answers `false`,
    an entry answers by its restart, and a former by its family. -/
theorem rightC_wit {NR : Nat} (dR : GSys τ NR) (P : Mean.V (B := S.sig) → Prop)
    (restart fam : Graph S.sig NR → Bool)
    (hr : ∀ j, restart (dR.sys j) = false →
      ∃ v, P v ∧ ((mng τ dR (.leaf j)).f o v).isSome = true)
    (hf : ∀ y, Frag setOk y = true → isFormer y = true → fam y = false →
      ∃ v, P v ∧ ((mng τ dR y).f o v).isSome = true) :
    ∀ y, Frag setOk y = true → rightC dR.sys restart fam y = false →
      ∃ v, P v ∧ ((mng τ dR y).f o v).isSome = true := by
  intro y
  induction y with
  | leaf j =>
    intro _ h
    simp only [rightC, Bool.or_eq_false_iff] at h
    exact hr j h.2
  | node op a ih =>
    intro hF h
    cases op with
    | never => exact nomatch h
    | refine _ _ => exact nomatch hF
    | union m =>
      simp only [rightC, Bool.or_eq_false_iff] at h
      simp only [Frag] at hF
      obtain ⟨p, -, hp⟩ := all_false h.2
      obtain ⟨v, h1, h2⟩ := ih p (List.all_eq_true.mp hF p (List.mem_finRange p)) hp
      exact ⟨v, h1, union_of dR p h2⟩
    | prim g => exact hf _ hF rfl h
    | set => exact hf _ hF rfl h
    | list _ _ _ => exact hf _ hF rfl h
    | obj _ _ _ => exact hf _ hF rfl h
    | opaq => exact nomatch hF
    | held _ _ _ => exact nomatch hF
    | legacy _ => exact nomatch hF


omit [Leaf S.sig] in
/-- A set element of the fragment is in the fragment. -/
theorem frag_of_elemFrag {N : Nat} (t : Graph S.sig N) :
    elemFrag setOk t = true → Frag setOk t = true := by
  induction t with
  | leaf _ => intro h; exact nomatch h
  | node op a ih =>
    intro h
    cases op with
    | prim _ => rfl
    | union m =>
      simp only [elemFrag] at h
      simp only [Frag]
      exact List.all_eq_true.mpr fun p hp => ih p (List.all_eq_true.mp h p hp)
    | _ => simp [elemFrag] at h

omit [Leaf S.sig] in
/-- **A set element of the fragment is a codec that a set holds.** -/
theorem setEl_of_elemFrag {N : Nat} (d : GSys τ N) (t : Graph S.sig N) :
    elemFrag setOk t = true → SetEl setOk (mng τ d t) := by
  induction t with
  | leaf _ => intro h; exact nomatch h
  | node op a ih =>
    intro h
    cases op with
    | prim g => exact SetEl.ground g h
    | union m =>
      simp only [elemFrag] at h
      refine SetEl.alt _ _ fun c hc => ?_
      obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hc
      exact ih p (List.all_eq_true.mp h p (List.mem_finRange p))
    | _ => simp [elemFrag] at h

omit [Sem S] [Leaf S.sig] in
/-- A pair below a guard with a closed side runs the row at the same fuel. -/
theorem pairX_node {NL NR : Nat} (sL : Fin NL → Graph S.sig NL) (sR : Fin NR → Graph S.sig NR)
    (prev : Tbl NL NR → Graph S.sig NL → Graph S.sig NR → Bool) (A : Tbl NL NR) {op : (TSig S.sig).Op}
    {a : (TSig S.sig).Pos op → Graph S.sig NL} (self : Graph S.sig NR → Bool) (y : Graph S.sig NR) :
    pairX (sL := sL) (sR := sR) prev A (.node op a) self y = self y := rfl

omit [Leaf S.sig] in
/-- The meaning of a set node is the lift of the meaning of its element. -/
theorem mng_set {N : Nat} (d : GSys τ N)
    {L : SetF (Mean.V (B := S.sig)) (Mean.Mem (B := S.sig)) Mean.mem Mean.d}
    (hs : Mean.set (B := S.sig) = some L) (a : (TOp.set (B := S.sig)).Pos → Graph S.sig N) :
    mng τ d (.node .set a) = L.lift (mng τ d (a ())) := by
  have e : mng τ d (.node .set a) = TOp.run τ .set (fun p => mng τ d (a p)) := rfl
  rw [e]
  simp only [TOp.run, hs]


omit [Leaf S.sig] in
/-- **Aligned witnesses are one list of data.** -/
theorem forall₂_wit {NL NR : Nat} {dL : GSys τ NL} {dR : GSys τ NR} {rowL : List (Graph S.sig NL)}
    {rowU : List (Graph S.sig NR)} (h : List.Forall₂ (Wit dL dR o) rowL rowU) :
    ∃ xs : List (Mean.V (B := S.sig)),
      List.Forall₂ (fun t x => ((mng τ dL t).f o x).isSome = true) rowL xs ∧
      List.Forall₂ (fun u x => ((mng τ dR u).f o x).isSome = true) rowU xs := by
  induction h with
  | nil => exact ⟨[], .nil, .nil⟩
  | cons hw _ ih =>
    obtain ⟨v, h1, h2⟩ := hw
    obtain ⟨xs, a, b⟩ := ih
    exact ⟨v :: xs, .cons h1 a, .cons h2 b⟩

omit [Leaf S.sig] in
/-- A traversal of codecs that each accept their datum succeeds. -/
theorem traverse_isSome_of_forall₂ {cs : List (Mean.C S.sig)} {xs : List (Mean.V (B := S.sig))}
    (h : List.Forall₂ (fun c x => (c.f o x).isSome = true) cs xs) :
    (traverse (fun cx : Mean.C S.sig × Mean.V (B := S.sig) => cx.1.f o cx.2) (cs.zip xs)).isSome = true := by
  induction h with
  | nil => rfl
  | cons hc _ ih =>
    rw [List.zip_cons_cons, traverse_cons_isSome, Bool.and_eq_true]
    exact ⟨hc, ih⟩

omit [Leaf S.sig] in
/-- **A list node accepts the list of data that its row accepts.** -/
theorem list_accepts {N : Nat} (d : GSys τ N)
    {L : ListA (Mean.V (B := S.sig)) (Mean.Mem (B := S.sig)) Mean.mem Mean.d}
    (hL : Mean.list (B := S.sig) = some L) {n m : Nat} {s' : Fin 2}
    (a : (TOp.list n s' m (B := S.sig)).Pos → Graph S.sig N) {len : Nat} {row : List (Graph S.sig N)}
    (hrow : rowOfG (listParts a).1 (listParts a).2.1 (listParts a).2.2 len = some row)
    {xs : List (Mean.V (B := S.sig))}
    (h : List.Forall₂ (fun t x => ((mng τ d t).f o x).isSome = true) row xs) :
    ((mng τ d (.node (.list n s' m) a)).f o (L.p.into xs)).isSome = true := by
  have e : mng τ d (.node (.list n s' m) a) = listCodec L.toSummand
      (List.ofFn fun p => mng τ d (a (.inl p))) (optOf s' fun p => mng τ d (a (.inr (.inl p))))
      (List.ofFn fun p => mng τ d (a (.inr (.inr p)))) := by
    rw [mng_list]; simp only [TOp.run, hL]
  have hlen : xs.length = len := by rw [← h.length_eq]; exact rowOfG_length hrow
  have hrow' : rowOfG (listParts a).1 (listParts a).2.1 (listParts a).2.2 xs.length = some row := by
    rw [hlen]; exact hrow
  rw [e, listCodec_f, L.p.out_into]
  simp only [Option.bind_some, Option.isSome_map]
  unfold alignL
  rw [slotsL_eq_rowOfG, rowOfG_listParts (mng τ d) a xs.length, hrow']
  simp only [Option.map_some, Option.bind_some]
  exact traverse_isSome_of_forall₂ (List.forall₂_map_left_iff.mpr h)

omit [Leaf S.sig] in
/-- **Two list nodes share a datum** where one common length has two rows of aligned shared
    data. -/
theorem list_wit {NL NR : Nat} (dL : GSys τ NL) (dR : GSys τ NR)
    {L : ListA (Mean.V (B := S.sig)) (Mean.Mem (B := S.sig)) Mean.mem Mean.d}
    (hL : Mean.list (B := S.sig) = some L) {n m n' m' : Nat} {s s' : Fin 2}
    (a : (TOp.list n s m (B := S.sig)).Pos → Graph S.sig NL)
    (b : (TOp.list n' s' m' (B := S.sig)).Pos → Graph S.sig NR) {len : Nat}
    {rowL : List (Graph S.sig NL)} {rowU : List (Graph S.sig NR)}
    (hl : rowOfG (listParts a).1 (listParts a).2.1 (listParts a).2.2 len = some rowL)
    (hu : rowOfG (listParts b).1 (listParts b).2.1 (listParts b).2.2 len = some rowU)
    (hw : List.Forall₂ (Wit dL dR o) rowL rowU) :
    Wit dL dR o (.node (.list n s m) a) (.node (.list n' s' m') b) := by
  obtain ⟨xs, h1, h2⟩ := forall₂_wit hw
  exact ⟨L.p.into xs, list_accepts dL hL a hl h1, list_accepts dR hL b hu h2⟩

/-- A walk whose answer `false` has a datum. -/
def Complete {NL NR : Nat} (dL : GSys τ NL) (dR : GSys τ NR) (o : Orient) (setOk : S.sig.Ground → Bool)
    (prev : Tbl NL NR → Graph S.sig NL → Graph S.sig NR → Bool) : Prop :=
  ∀ A x y, Frag setOk x = true → Frag setOk y = true → prev A x y = false → Wit dL dR o x y


omit [Leaf S.sig] in
/-- A term and its entry share the data of the entry. -/
theorem wit_leaf_left {NL NR : Nat} {dL : GSys τ NL} {dR : GSys τ NR} {j : Fin NL}
    {y : Graph S.sig NR} (h : Wit dL dR o (dL.sys j) y) : Wit dL dR o (.leaf j) y := by
  obtain ⟨v, h1, h2⟩ := h
  exact ⟨v, by rw [mng_leaf]; exact h1, h2⟩

omit [Leaf S.sig] in
/-- The same at the right operand. -/
theorem wit_leaf_right {NL NR : Nat} {dL : GSys τ NL} {dR : GSys τ NR} {x : Graph S.sig NL}
    {j : Fin NR} (h : Wit dL dR o x (dR.sys j)) : Wit dL dR o x (.leaf j) := by
  obtain ⟨v, h1, h2⟩ := h
  exact ⟨v, h1, by rw [mng_leaf]; exact h2⟩

omit [Leaf S.sig] in
/-- A list node of the fragment has a list former and a fragment term at each position. -/
theorem frag_list {N n m : Nat} {s : Fin 2} {a : (TOp.list n s m (B := S.sig)).Pos → Graph S.sig N}
    (h : Frag setOk (.node (.list n s m) a) = true) :
    (Mean.list (B := S.sig)).isSome = true ∧ ∀ q, Frag setOk (a q) = true := by
  simp only [Frag, Bool.and_eq_true] at h
  exact ⟨h.1, fun q => List.all_eq_true.mp h.2 ⟨q, TOp.pos_complete _ q⟩ (List.mem_attach _ _)⟩

omit [Leaf S.sig] in
/-- An object node of the fragment has a map former, no fill and a fragment term at each
    position. -/
theorem frag_obj {N : Nat} {fs : Finset String} {md : {x // x ∈ fs} → SlotMode S.sig} {w : Fin 2}
    {a : (TOp.obj fs md w (B := S.sig)).Pos → Graph S.sig N}
    (h : Frag setOk (.node (.obj fs md w) a) = true) :
    (Mean.map (B := S.sig)).isSome = true ∧ (∀ x, md x = .req ∨ md x = .opt) ∧
      (∀ q, Frag setOk (a q) = true) := by
  simp only [Frag, Bool.and_eq_true] at h
  refine ⟨h.1.1, fun x => ?_, fun q => List.all_eq_true.mp h.2 ⟨q, TOp.pos_complete _ q⟩ (List.mem_attach _ _)⟩
  have h2 := h.1.2
  simp only [TOp.adapts, Bool.not_eq_true', List.any_eq_false] at h2
  have := h2 x (keyPos_complete fs x)
  cases hm : md x with
  | req => exact Or.inl rfl
  | opt => exact Or.inr rfl
  | fill _ => rw [hm] at this; exact absurd rfl this

/-- **The test of a pair below a guard is complete.** -/
theorem pairX_wit {NL NR : Nat} (dL : GSys τ NL) (dR : GSys τ NR)
    (hL : ∀ i, Frag setOk (dL.sys i) = true) (hR : ∀ j, Frag setOk (dR.sys j) = true)
    (prev : Tbl NL NR → Graph S.sig NL → Graph S.sig NR → Bool)
    (hp : Complete dL dR o setOk prev) (A : Tbl NL NR) (t : Graph S.sig NL) (u : Graph S.sig NR)
    (hu : Frag setOk u = true) (ht : Frag setOk t = true)
    (ih : ∀ y, Frag setOk y = true → rowG dL.sys dR.sys prev A t y = false → Wit dL dR o t y)
    (h : pairX (sL := dL.sys) (sR := dR.sys) prev A t (rowG dL.sys dR.sys prev A t) u = false) :
    Wit dL dR o t u := by
  cases t with
  | leaf i =>
    cases u with
    | leaf j =>
      simp only [pairX, Bool.or_eq_false_iff] at h
      exact wit_leaf_left (wit_leaf_right (hp _ _ _ (hL i) (hR j) h.2))
    | node op b => exact ih _ hu h
  | node op a => exact ih _ hu h

omit [Leaf S.sig] in
/-- The fragment term of the slot that an object node gives one name. -/
theorem frag_slotAtG {N : Nat} {fs : Finset String} {md : {x // x ∈ fs} → SlotMode S.sig} {w : Fin 2}
    {a : (TOp.obj fs md w (B := S.sig)).Pos → Graph S.sig N}
    (ha : ∀ q, Frag setOk (a q) = true) (n : String) :
    Frag setOk (slotAtG (md := md) a n).2 = true := by
  unfold slotAtG
  split
  · exact ha _
  · match w, a, ha with
    | ⟨0, _⟩, _, _ => rfl
    | ⟨1, _⟩, a, ha => exact ha _

omit [Leaf S.sig] in
/-- **An object node accepts the map that its slots accept.** -/
theorem obj_accepts {N : Nat} (d : GSys τ N)
    {F : MapA (Mean.V (B := S.sig)) (Mean.Mem (B := S.sig)) Mean.mem Mean.d}
    (hF : Mean.map (B := S.sig) = some F) {fs : Finset String} {md : {x // x ∈ fs} → SlotMode S.sig}
    {w : Fin 2} (a : (TOp.obj fs md w (B := S.sig)).Pos → Graph S.sig N)
    (hmd : ∀ x, md x = .req ∨ md x = .opt) (p : MapOf (Mean.V (B := S.sig)))
    (hreq : ∀ x : {x // x ∈ fs}, md x = .req → x.1 ∈ p.keys)
    (hent : ∀ k : {k // k ∈ p.keys},
      ((mng τ d (slotAtG (md := md) a k.1).2).f o (p.get k)).isSome = true) :
    ((mng τ d (.node (.obj fs md w) a)).f o (F.p.into p)).isSome = true := by
  have e : mng τ d (.node (.obj fs md w) a) = objectCodec F.toSummand
      ⟨fs, fun x => mkField (md x) (mng τ d (a (.inl x)))⟩ (restOf w fun p => mng τ d (a (.inr p))) := by
    have e0 : mng τ d (.node (.obj fs md w) a) = TOp.run τ (.obj fs md w) (fun p => mng τ d (a p)) := rfl
    rw [e0]; simp only [TOp.run, hF]
  rw [e, objectCodec_f, F.p.out_into]
  simp only [Option.bind_some, Option.isSome_map]
  refine objAt_isSome.mpr ⟨fun k hk hkp => ?_, fun k => ?_⟩
  · rw [MapOf.at_of_mem (m := ⟨fs, _⟩) ⟨k, hk⟩]
    simp only
    rcases hmd ⟨k, hk⟩ with h | h
    · exact absurd (hreq ⟨k, hk⟩ h) hkp
    · rw [h]; rfl
  · rw [entry_slot d a k.1 (p.get k)]
    exact hent k

/-- **A witness for each name of a list is one association list.** -/
theorem exists_assoc {V : Type} {P : String → V → Prop} :
    ∀ l : List String, (∀ n ∈ l, ∃ v, P n v) →
      ∃ g : List (String × V), ∀ n ∈ l, ∃ v, g.lookup n = some v ∧ P n v
  | [], _ => ⟨[], fun _ h => nomatch h⟩
  | n :: l, h => by
    obtain ⟨g, hg⟩ := exists_assoc l fun m hm => h m (List.mem_cons_of_mem _ hm)
    obtain ⟨v, hv⟩ := h n List.mem_cons_self
    refine ⟨(n, v) :: g, fun m hm => ?_⟩
    rcases Decidable.em (m = n) with rfl | hne
    · exact ⟨v, by simp [List.lookup], hv⟩
    · rcases List.mem_cons.mp hm with rfl | hm
      · exact absurd rfl hne
      · obtain ⟨w, hw1, hw2⟩ := hg m hm
        have hb : (m == n) = false := by simpa using hne
        exact ⟨w, by simp [List.lookup, hb, hw1], hw2⟩

/-- Whether an object requires a name: the name is declared, and its slot requires it. -/
def reqS {fs : Finset String} (md : {x // x ∈ fs} → SlotMode S.sig) (n : String) : Bool :=
  if h : n ∈ fs then (md ⟨n, h⟩).isReq else false

omit [Sem S] [Leaf S.sig] in
/-- A name that an object requires is a name that the object declares. -/
theorem mem_of_reqS {fs : Finset String} {md : {x // x ∈ fs} → SlotMode S.sig} {n : String}
    (h : reqS md n = true) : n ∈ fs := by
  unfold reqS at h
  split at h
  · assumption
  · exact nomatch h

omit [Leaf S.sig] in
/-- **Two object nodes share a datum** where the slots of the two nodes share a datum at each name
    that one of the two requires. -/
theorem obj_wit {NL NR : Nat} (dL : GSys τ NL) (dR : GSys τ NR)
    {F : MapA (Mean.V (B := S.sig)) (Mean.Mem (B := S.sig)) Mean.mem Mean.d}
    (hF : Mean.map (B := S.sig) = some F) {fs fs' : Finset String}
    {md : {x // x ∈ fs} → SlotMode S.sig} {md' : {x // x ∈ fs'} → SlotMode S.sig} {w w' : Fin 2}
    (a : (TOp.obj fs md w (B := S.sig)).Pos → Graph S.sig NL)
    (b : (TOp.obj fs' md' w' (B := S.sig)).Pos → Graph S.sig NR)
    (hmd : ∀ x, md x = .req ∨ md x = .opt) (hmd' : ∀ x, md' x = .req ∨ md' x = .opt)
    (hW : ∀ n, (reqS md n || reqS md' n) = true →
      Wit dL dR o (slotAtG (md := md) a n).2 (slotAtG (md := md') b n).2) :
    Wit dL dR o (.node (.obj fs md w) a) (.node (.obj fs' md' w') b) := by
  let P : String → Mean.V (B := S.sig) → Prop := fun n v =>
    ((mng τ dL (slotAtG (md := md) a n).2).f o v).isSome = true ∧
      ((mng τ dR (slotAtG (md := md') b n).2).f o v).isSome = true
  let l : List String := (keysOf fs ++ keysOf fs').filter fun n => reqS md n || reqS md' n
  have hl : ∀ n ∈ l, (reqS md n || reqS md' n) = true ∧ ∃ v, P n v := by
    intro n hn
    have hK := (List.mem_filter.mp hn).2
    exact ⟨hK, hW n hK⟩
  obtain ⟨gl, hgl⟩ := exists_assoc (P := P) l fun n hn => (hl n hn).2
  let g : String → Option (Mean.V (B := S.sig)) := fun n =>
    if (reqS md n || reqS md' n) = true then gl.lookup n else none
  let p : MapOf (Mean.V (B := S.sig)) := MapOf.ofFun (fs ∪ fs') g
  have hmemL : ∀ n, (reqS md n || reqS md' n) = true → n ∈ l := by
    intro n hK
    refine List.mem_filter.mpr ⟨?_, hK⟩
    rcases Bool.or_eq_true_iff.mp hK with h | h
    · exact List.mem_append.mpr (Or.inl (mem_keysOf.mpr (mem_of_reqS h)))
    · exact List.mem_append.mpr (Or.inr (mem_keysOf.mpr (mem_of_reqS h)))
  have hmem : ∀ n, n ∈ p.keys ↔ (reqS md n || reqS md' n) = true := by
    intro n
    simp only [p, MapOf.ofFun, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨-, hs⟩
      by_cases hK : (reqS md n || reqS md' n) = true
      · exact hK
      · simp only [g, if_neg hK] at hs; exact nomatch hs
    · intro hK
      obtain ⟨v, hlk, -⟩ := hgl n (hmemL n hK)
      refine ⟨?_, by simp only [g, if_pos hK, hlk]; rfl⟩
      rcases Bool.or_eq_true_iff.mp hK with h | h
      · exact Or.inl (mem_of_reqS h)
      · exact Or.inr (mem_of_reqS h)
  have hget : ∀ (n : String) (hn : n ∈ p.keys), P n (p.get ⟨n, hn⟩) := by
    intro n hn
    have hK := (hmem n).mp hn
    obtain ⟨v, hlk, hP⟩ := hgl n (hmemL n hK)
    have hgv : g n = some v := by simp only [g, if_pos hK, hlk]
    have : p.get ⟨n, hn⟩ = v := by
      simp only [p, MapOf.ofFun]
      simp only [hgv]
      rfl
    rw [this]; exact hP
  refine ⟨F.p.into p, obj_accepts dL hF a hmd p (fun x hx => ?_) (fun k => (hget k.1 k.2).1),
    obj_accepts dR hF b hmd' p (fun x hx => ?_) (fun k => (hget k.1 k.2).2)⟩
  · refine (hmem x.1).mpr ?_
    simp [reqS, x.2, hx, SlotMode.isReq]
  · refine (hmem x.1).mpr ?_
    simp [reqS, x.2, hx, SlotMode.isReq]

omit [Sem S] [Leaf S.sig] in
/-- **A block test that answers `false` reads a position of the block**, and an undeclared name has
    that position as its slot. -/
theorem blockX_slot {N M : Nat} {fs : Finset String} {md : {x // x ∈ fs} → SlotMode S.sig}
    (w : Fin 2) (a : (TOp.obj fs md w (B := S.sig)).Pos → Graph S.sig N) {n : String} (hn : n ∉ fs)
    (T : Graph S.sig N → Graph S.sig M → Bool) (u : Graph S.sig M)
    (h : blockX (md := md) w (fun p => T (a p)) u = false) :
    ∃ q, a q = (slotAtG (md := md) a n).2 ∧ T (a q) u = false := by
  match w, a, h with
  | ⟨0, _⟩, _, h => exact nomatch h
  | ⟨1, _⟩, a, h =>
    refine ⟨.inr ⟨0, Nat.one_pos⟩, ?_, h⟩
    unfold slotAtG; rw [dif_neg hn]

/-- A relation between two lists, kept on the members of the lists. -/
theorem forall₂_of_mem {X Y : Type} {R Q : X → Y → Prop} {l : List X} {l' : List Y}
    (h : List.Forall₂ R l l') (hq : ∀ x y, x ∈ l → y ∈ l' → R x y → Q x y) : List.Forall₂ Q l l' := by
  induction h with
  | nil => exact .nil
  | cons hr _ ih =>
    exact .cons (hq _ _ List.mem_cons_self List.mem_cons_self hr)
      (ih fun x y hx hy => hq x y (List.mem_cons_of_mem _ hx) (List.mem_cons_of_mem _ hy))


/-- **A row is complete** where the walk that it reads is complete. -/
theorem row_wit {NL NR : Nat} (dL : GSys τ NL) (dR : GSys τ NR) (wl : WLaws S o setOk)
    (hL : ∀ i, Frag setOk (dL.sys i) = true) (hR : ∀ j, Frag setOk (dR.sys j) = true)
    (prev : Tbl NL NR → Graph S.sig NL → Graph S.sig NR → Bool)
    (hp : Complete dL dR o setOk prev) (A : Tbl NL NR) :
    ∀ x, Frag setOk x = true → ∀ y, Frag setOk y = true →
      rowG dL.sys dR.sys prev A x y = false → Wit dL dR o x y := by
  intro x
  induction x with
  | leaf j =>
    intro _ y hy h
    exact wit_leaf_left (hp A _ y (hL j) hy h)
  | node op a ih =>
    intro hx y hy h
    -- the restart of a row that reads the right operand
    have hrestart : ∀ j, prev A (.node op a) (dR.sys j) = false →
        ∃ v, ((mng τ dL (.node op a)).f o v).isSome = true ∧
          ((mng τ dR (.leaf j)).f o v).isSome = true := fun j hj =>
      (wit_leaf_right (hp A _ _ hx (hR j) hj))
    cases op with
    | never => exact nomatch h
    | refine _ _ => exact nomatch hx
    | opaq => exact nomatch hx
    | held _ _ _ => exact nomatch hx
    | legacy _ => exact nomatch hx
    | union m =>
      simp_rowG at h
      simp only [Frag] at hx
      obtain ⟨p, -, hp'⟩ := all_false h
      obtain ⟨v, h1, h2⟩ := ih p (List.all_eq_true.mp hx p (List.mem_finRange p)) y hy hp'
      exact ⟨v, union_of dL p h1, h2⟩
    | prim g =>
      simp_rowG at h
      refine rightC_wit dR _ _ _ hrestart ?_ y hy h
      intro y' _ hf hfam
      cases y' with
      | leaf _ => exact nomatch hf
      | node op' b =>
        cases op' with
        | prim g' =>
          obtain ⟨v, h1, h2⟩ := wl.prim g g' hfam
          exact ⟨v, h1, h2⟩
        | set => exact nomatch hfam
        | list _ _ _ => exact nomatch hfam
        | obj _ _ _ => exact nomatch hfam
        | _ => exact nomatch hf
    | set =>
      simp_rowG at h
      refine rightC_wit dR _ _ _ hrestart ?_ y hy h
      intro y' hy' hf hfam
      cases y' with
      | leaf _ => exact nomatch hf
      | node op' b =>
        cases op' with
        | set =>
          simp only [Frag, Bool.and_eq_true] at hx hy'
          simp only [famSetG] at hfam
          have hf1 : Frag setOk (a ()) = true := frag_of_elemFrag _ hx.2
          have hf2 : Frag setOk (b ()) = true := frag_of_elemFrag _ hy'.2
          have hpair : rowG dL.sys dR.sys prev A (a ()) (b ()) = false := by
            cases ha : a () with
            | leaf _ => rw [ha] at hf1; exact absurd hx.2 (by rw [ha]; simp [elemFrag])
            | node opa a' => rw [ha] at hfam; exact hfam
          obtain ⟨u, hu1, hu2⟩ := ih () hf1 _ hf2 hpair
          cases hs : Mean.set (B := S.sig) with
          | none => rw [hs] at hx; exact nomatch hx.1
          | some L =>
            obtain ⟨v, hv1, hv2⟩ := wl.set L hs _ _ (setEl_of_elemFrag dL _ hx.2)
              (setEl_of_elemFrag dR _ hy'.2) ⟨u, hu1, hu2⟩
            exact ⟨v, (congrArg (fun c => ((c.f o v).isSome = true)) (mng_set dL hs a)).mpr hv1,
              (congrArg (fun c => ((c.f o v).isSome = true)) (mng_set dR hs b)).mpr hv2⟩
        | prim _ => exact nomatch hfam
        | list _ _ _ => exact nomatch hfam
        | obj _ _ _ => exact nomatch hfam
        | _ => exact nomatch hf
    | list n s m =>
      simp_rowG at h
      obtain ⟨hLsome, hfq⟩ := frag_list hx
      refine rightC_wit dR _ _ _ hrestart ?_ y hy h
      intro y' hy' hf hfam
      cases y' with
      | leaf _ => exact nomatch hf
      | node op' b =>
        cases op' with
        | list n' s' m' =>
          obtain ⟨-, hgq⟩ := frag_list hy'
          cases hl : Mean.list (B := S.sig) with
          | none => rw [hl] at hLsome; exact nomatch hLsome
          | some L =>
            simp only [famListG] at hfam
            have e := listPartsX_eq a (fun x => pairX (sL := dL.sys) (sR := dR.sys) prev A x
              (rowG dL.sys dR.sys prev A x))
            rw [e] at hfam
            obtain ⟨len, fs, us, hfs, hus, hz⟩ := listRowG_false hfam
            rw [rowOfG_map] at hfs
            obtain ⟨rowL, hrowL, rfl⟩ := Option.map_eq_some_iff.mp hfs
            have hlen : (rowL.map fun x => pairX (sL := dL.sys) (sR := dR.sys) prev A x
                (rowG dL.sys dR.sys prev A x)).length = us.length := by
              rw [List.length_map, rowOfG_length hrowL, rowOfG_length hus]
            have hz' := List.forall₂_map_left_iff.mp (anyZipG_false hlen hz)
            have hW := forall₂_of_mem hz' fun t u ht hu hT => by
              obtain ⟨q, rfl⟩ := listParts_mem a (rowOfG_mem hrowL t ht)
              obtain ⟨q', rfl⟩ := listParts_mem b (rowOfG_mem hus u hu)
              exact pairX_wit dL dR hL hR prev hp A _ _ (hgq q') (hfq q)
                (fun y hy' hr => ih q (hfq q) y hy' hr) hT
            exact list_wit dL dR hl a b hrowL hus hW
        | prim _ => exact nomatch hfam
        | set => exact nomatch hfam
        | obj _ _ _ => exact nomatch hfam
        | _ => exact nomatch hf
    | obj fs md w =>
      simp_rowG at h
      obtain ⟨hMsome, hmd, hfq⟩ := frag_obj hx
      refine rightC_wit dR _ _ _ hrestart ?_ y hy h
      intro y' hy' hf hfam
      cases y' with
      | leaf _ => exact nomatch hf
      | node op' b =>
        cases op' with
        | obj fs' md' w' =>
          obtain ⟨-, hmd', hgq⟩ := frag_obj hy'
          cases hM : Mean.map (B := S.sig) with
          | none => rw [hM] at hMsome; exact nomatch hMsome
          | some F =>
            simp only [famObjG, Bool.or_eq_false_iff, List.any_eq_false] at hfam
            refine obj_wit dL dR hM a b hmd hmd' ?_
            intro n hK
            rcases Decidable.em (n ∈ fs) with hn | hn
            · have hg : ((md ⟨n, hn⟩).isReq ||
                  (slotAtG (md := md') b n).1.isReq) = true := by
                have hK' : (reqS md n || reqS md' n) = true := hK
                simp only [reqS, dif_pos hn, Bool.or_eq_true] at hK' ⊢
                rcases hK' with h1 | h1
                · exact Or.inl h1
                · rcases Decidable.em (n ∈ fs') with h' | h'
                  · rw [dif_pos h'] at h1
                    refine Or.inr ?_
                    rw [slotAtG_mem b ⟨n, h'⟩]; exact h1
                  · rw [dif_neg h'] at h1; exact nomatch h1
              have hT := hfam.1 ⟨n, hn⟩ (keyPos_complete fs _)
              simp only [Bool.and_eq_true, hg, true_and] at hT
              have hT' : pairX (sL := dL.sys) (sR := dR.sys) prev A (a (.inl ⟨n, hn⟩))
                  (rowG dL.sys dR.sys prev A (a (.inl ⟨n, hn⟩))) (slotAtG (md := md') b n).2 = false := by
                simpa using hT
              rw [slotAtG_mem a ⟨n, hn⟩]
              exact pairX_wit dL dR hL hR prev hp A _ _ (frag_slotAtG hgq n) (hfq _)
                (fun y hy' hr => ih _ (hfq _) y hy' hr) hT'
            · have hK' : (reqS md n || reqS md' n) = true := hK
              have h1 : reqS md n = false := by simp [reqS, hn]
              rw [h1, Bool.false_or] at hK'
              have h' := mem_of_reqS hK'
              have hr : (md' ⟨n, h'⟩).isReq = true := by simpa [reqS, h'] using hK'
              have hT := hfam.2 ⟨n, h'⟩ (keyPos_complete fs' _)
              have hmw : blockX (md := md) w (fun p => pairX (sL := dL.sys) (sR := dR.sys) prev A (a p)
                  (rowG dL.sys dR.sys prev A (a p))) (b (.inl ⟨n, h'⟩)) = false := by
                simp only [hr, hn, Bool.and_eq_true, decide_false, Bool.not_false, true_and] at hT
                simpa using hT
              obtain ⟨q, hq, hqT⟩ := blockX_slot w a hn
                (fun x => pairX (sL := dL.sys) (sR := dR.sys) prev A x (rowG dL.sys dR.sys prev A x))
                _ hmw
              rw [slotAtG_mem b ⟨n, h'⟩, ← hq]
              exact pairX_wit dL dR hL hR prev hp A _ _ (hgq _) (hfq q)
                (fun y hy' hr => ih q (hfq q) y hy' hr) hqT
        | prim _ => exact nomatch hfam
        | set => exact nomatch hfam
        | list _ _ _ => exact nomatch hfam
        | _ => exact nomatch hf


/-- **Completeness of the optimistic walk**: over the fragment, an answer `false` at any fuel and
    any table has a common datum. -/
theorem decO_complete {NL NR : Nat} (dL : GSys τ NL) (dR : GSys τ NR) (wl : WLaws S o setOk)
    (hL : ∀ i, Frag setOk (dL.sys i) = true) (hR : ∀ j, Frag setOk (dR.sys j) = true) :
    ∀ n, Complete dL dR o setOk (decO dL.sys dR.sys n)
  | 0 => fun _ _ _ _ _ h => nomatch h
  | n + 1 => fun A x y hx hy h =>
    row_wit dL dR wl hL hR (decO dL.sys dR.sys n) (decO_complete dL dR wl hL hR n) A x hx y hy h

end Wit

section Exact
variable {S : Syn} [Sem S] [Leaf S.sig] [Shapes S]
  {τ : (s : Bool) → TableAt S.sig s} {o : Orient} {setOk : S.sig.Ground → Bool}

omit [Shapes S] in
/-- **A refused pair has a common datum.** Two closed codecs of the fragment that `disjoint` does not
    separate both accept one datum. -/
theorem disjoint_false_witness (wl : WLaws S o setOk) {NL NR : Nat}
    {dL : Closed S.sig NL} {dR : Closed S.sig NR} {rL : Fin NL} {rR : Fin NR}
    (hL : ∀ i, Frag setOk (dL.graph i) = true) (hR : ∀ j, Frag setOk (dR.graph j) = true)
    (hd : disjoint dL rL dR rR = false) : ∃ v : Mean.V (B := S.sig),
      ((Closed.meaning τ dL rL).f o v).isSome = true ∧ ((Closed.meaning τ dR rR).f o v).isSome = true := by
  have hO : decO dL.graph dR.graph (fuel NL NR) [] (.leaf rL) (.leaf rR) = false := by
    cases hc : decO dL.graph dR.graph (fuel NL NR) [] (.leaf rL) (.leaf rR) with
    | false => rfl
    | true =>
      have := decO_fuel_imp_decG dL.graph dR.graph (fun i => i.val) (fun j => j.val)
        (Closed.fueled dL dR) rL rR hc
      rw [disjoint] at hd
      rw [hd] at this
      exact nomatch this
  obtain ⟨v, h1, h2⟩ := decO_complete (Closed.toG τ dL) (Closed.toG τ dR) wl hL hR _ [] _ _ rfl rfl hO
  exact ⟨v, h1, h2⟩

/-- **The decision is exact over the fragment.** Two closed codecs of the fragment share no datum
    exactly where `disjoint` answers `true`. The universe supplies the laws of the decision and
    their duals. -/
theorem disjoint_exact (laws : Laws S o) (wl : WLaws S o setOk) {NL NR : Nat}
    {dL : Closed S.sig NL} {dR : Closed S.sig NR} {rL : Fin NL} {rR : Fin NR}
    (hL : ∀ i, Frag setOk (dL.graph i) = true) (hR : ∀ j, Frag setOk (dR.graph j) = true) :
    disjoint dL rL dR rR = true ↔ ∀ v : Mean.V (B := S.sig),
      (((Closed.meaning τ dL rL).f o v).isSome && ((Closed.meaning τ dR rR).f o v).isSome) = false := by
  refine ⟨fun h v => disjoint_sound laws h v, fun h => ?_⟩
  cases hd : disjoint dL rL dR rR with
  | true => rfl
  | false =>
    exfalso
    obtain ⟨v, h1, h2⟩ := disjoint_false_witness (τ := τ) wl hL hR hd
    have := h v
    rw [h1, h2] at this
    exact nomatch this

/-- **Inhabitation is the self disjointness.** A closed codec of the fragment accepts a datum
    exactly where `disjoint` answers `false` at the pair of the codec with itself. -/
theorem inhabited_iff (laws : Laws S o) (wl : WLaws S o setOk) {N : Nat}
    {d : Closed S.sig N} {r : Fin N} (h : ∀ i, Frag setOk (d.graph i) = true) :
    (∃ v : Mean.V (B := S.sig), ((Closed.meaning τ d r).f o v).isSome = true) ↔
      disjoint d r d r = false := by
  constructor
  · rintro ⟨v, hv⟩
    cases hd : disjoint d r d r with
    | false => rfl
    | true =>
      have := disjoint_sound (τ := τ) laws hd v
      rw [hv] at this
      exact nomatch this
  · intro hd
    obtain ⟨v, h1, _⟩ := disjoint_false_witness (τ := τ) wl h h hd
    exact ⟨v, h1⟩

end Exact

end Calculus.Alg.Scoped
