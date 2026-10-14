import Calculus.Lang.Scope
import Calculus.Lang.Universe
import Calculus.Alg.Rows

/-!
# Disjointness over the graph of a closed codec

`Scoped.disjoint` decides that two closed codecs share no datum. The decision reads the flat graph
of each closed codec, with one row per operation of the left operand. Below a guard, the decision assumes a pair of entries while it compares the two
bodies. At an unguarded position, the decision unfolds an entry. A fuel bounds the walk, so the
recursion is structural, and an empty fuel answers `false`.

`Scoped.disjoint_sound` states the soundness: where the decision answers `true`, no datum of any
depth is accepted by both meanings at the orientation. The proof is an induction on the fuel, and
at each pair below a guard an induction on the depth of the datum: the decision assumes a pair only
at a smaller depth. An unfolding reads the fixed point of the system. The laws of a universe enter
at the codecs: the primitive law and the set law (`Laws`), and the shape classes (`Shapes`). A
refinement accepts a part of what its inner term accepts, so the decision reads through a
refinement and reads no predicate.

`viewG` is the view of a graph term at an orientation, one clause per operation, and an entry stays
an entry. `Scoped.views_apart` states that two closed codecs whose views the decision separates
accept no common datum: each entry of the view accepts what the entry accepts (`view_entries`).
-/

namespace Calculus.Alg.Scoped

variable {B : Sig}

/-! ## The adapters that a graph term reaches -/

section Adapters
variable {N : Nat}

/-- An operation that reads its argument through caller code: a `held`, a `legacy`, or an
    object with a `fill`. -/
def TOp.adapts : TOp B → Bool
  | .held _ _ _ | .legacy _ => true
  | .obj fs md _ => (keyPos fs).any fun x => match md x with
    | .fill _ => true
    | _ => false
  | _ => false

/-- Whether a graph term reaches an adapter, where `ad` answers at each entry. -/
def Graph.adapts (ad : Fin N → Bool) : Graph B N → Bool
  | .leaf j => ad j
  | .node o a => o.adapts || o.pos.any fun p => Graph.adapts ad (a p)

/-- The entries that reach an adapter in `n` steps. -/
def adIter (sys : Fin N → Graph B N) : Nat → Fin N → Bool
  | 0 => fun _ => false
  | n + 1 => fun i => (sys i).adapts (adIter sys n)

/-- The entries that reach an adapter. -/
def adOf (sys : Fin N → Graph B N) : Fin N → Bool := adIter sys N

/-- Whether the table of adapters is a fixed point of the system. -/
def adStable (sys : Fin N → Graph B N) : Bool :=
  (List.finRange N).all fun i => (sys i).adapts (adOf sys) == adOf sys i

/-- **A graph term below the top**: the term reaches no adapter. -/
def belowTop (sys : Fin N → Graph B N) (t : Graph B N) : Bool :=
  adStable sys && !t.adapts (adOf sys)

end Adapters

/-! ## The rows -/

section Rows
variable [Leaf B] {NL NR : Nat} (sL : Fin NL → Graph B NL) (sR : Fin NR → Graph B NR)

/-- The table of the pairs of entries assumed apart. -/
abbrev Tbl (NL NR : Nat) := List (Fin NL × Fin NR)

/-- The bottom as a graph term. -/
def Graph.never {N : Nat} : Graph B N := .node .never fun p => nomatch p

/-- **The rows of the right operand.** `fam` answers each term first. The bottom admits nothing,
    and agrees with every term. A union is read where each option is, and a refinement where its
    inner term is. An entry unfolds through `restart`. -/
def rightC (restart fam : Graph B NR → Bool) : Graph B NR → Bool
  | .leaf j => fam (.leaf j) || restart (sR j)
  | .node .never _ => true
  | .node (.refine q qA) a => fam (.node (.refine q qA) a) || rightC restart fam (a ())
  | .node (.union m) a => fam (.node (.union m) a) ||
      (List.finRange m).all fun p => rightC restart fam (a p)
  | y => fam y

/-- A primitive beside a primitive the leaf keeps apart, or beside a former. -/
def famPrimG (g : B.Ground) : Graph B NR → Bool
  | .node (.prim g') _ => Leaf.primsApart g g'
  | .node .set _ | .node (.list _ _ _) _ | .node (.obj _ _ _) _ => true
  | _ => false

/-- A set beside a set whose element is apart, or beside a former of another class. -/
def famSetG (mt : Graph B NR → Bool) : Graph B NR → Bool
  | .node .set a => mt (a ())
  | .node (.prim _) _ | .node (.list _ _ _) _ | .node (.obj _ _ _) _ => true
  | _ => false

/-- Some position of two aligned rows is disjoint. -/
def anyZipG {X : Type} : List (X → Bool) → List X → Bool
  | f :: fs, u :: us => f u || anyZipG fs us
  | _, _ => false

/-- **Two list shapes**: one disjoint position at each common length. -/
def listRowG {X : Type} (fpre : List (X → Bool)) (fsp : Option (X → Bool))
    (fsuf : List (X → Bool)) (pre₂ : List X) (sp₂ : Option X) (suf₂ : List X) : Bool :=
  match fsp, sp₂ with
  | some f, some c =>
      if dominates fpre.length fsuf.length pre₂.length suf₂.length then
        match rowOfG fpre (some f) fsuf (max fpre.length pre₂.length + max fsuf.length suf₂.length),
            rowOfG pre₂ (some c) suf₂ (max fpre.length pre₂.length + max fsuf.length suf₂.length) with
        | some fs, some us => anyZipG fs us
        | _, _ => false
      else false
  | none, _ =>
      match rowOfG pre₂ sp₂ suf₂ (fpre.length + fsuf.length) with
      | some us => anyZipG (fpre ++ fsuf) us
      | none => true
  | some f, none =>
      match rowOfG fpre (some f) fsuf (pre₂.length + suf₂.length) with
      | some fs => anyZipG fs (pre₂ ++ suf₂)
      | none => true

/-- The positions of a list node, as a prefix, a spread and a suffix. -/
def listParts {N : Nat} {a : Nat} {s : Fin 2} {b : Nat}
    (g : TOp.Pos (B := B) (.list a s b) → Graph B N) :
    List (Graph B N) × Option (Graph B N) × List (Graph B N) :=
  (List.ofFn fun p => g (.inl p), optOf s (fun p => g (.inr (.inl p))),
    List.ofFn fun p => g (.inr (.inr p)))

/-- The family of a list: the rows against a list, and every former of another class. -/
def famListG (fpre : List (Graph B NR → Bool)) (fsp : Option (Graph B NR → Bool))
    (fsuf : List (Graph B NR → Bool)) : Graph B NR → Bool
  | .node (.list _ _ _) b =>
      listRowG fpre fsp fsuf (listParts b).1 (listParts b).2.1 (listParts b).2.2
  | .node (.prim _) _ | .node .set _ | .node (.obj _ _ _) _ => true
  | _ => false

/-- The slot that an object node gives one name: the declared slot, or `optional` of the block. -/
def slotAtG {N : Nat} {fs : Finset String} {md : {x // x ∈ fs} → SlotMode B} {s : Fin 2}
    (g : TOp.Pos (B := B) (.obj fs md s) → Graph B N) (k : String) : SlotMode B × Graph B N :=
  if h : k ∈ fs then (md ⟨k, h⟩, g (.inl ⟨k, h⟩))
  else (.opt, match s with
    | ⟨0, _⟩ => Graph.never
    | ⟨1, _⟩ => g (.inr ⟨0, Nat.one_pos⟩))

/-- Whether a slot mode requires the name. -/
def SlotMode.isReq : SlotMode B → Bool
  | .req => true
  | _ => false

/-- The family of an object: one name holds two slots apart, one of them required. -/
def famObjG {fs : Finset String} {md : {x // x ∈ fs} → SlotMode B}
    (g : {x // x ∈ fs} → Graph B NR → Bool) (mw : Graph B NR → Bool) : Graph B NR → Bool
  | .node (.obj fs' md' s') b =>
      (keyPos fs).any (fun k => ((md k).isReq || (slotAtG (md := md') b k.1).1.isReq) && g k (slotAtG (md := md') b k.1).2) ||
      (keyPos fs').any fun k => !decide (k.1 ∈ fs) && (md' k).isReq && mw (b (.inl k))
  | .node (.prim _) _ | .node .set _ | .node (.list _ _ _) _ => true
  | _ => false

variable {sL sR}

/-- A pair of positions below a guard: a pair of entries already assumed is apart, and a new
    pair is assumed while the walk compares the two bodies. -/
def pairAt (prev : Tbl NL NR → Graph B NL → Graph B NR → Bool) (A : Tbl NL NR) :
    Graph B NL → Graph B NR → Bool
  | .leaf i, .leaf j => A.any (fun p => decide (p.1 = i) && decide (p.2 = j)) ||
      prev ((i, j) :: A) (sL i) (sR j)
  | a, b => prev A a b

/-- The test of the open block of a left object: `true` where the object has no block. -/
def blockTest (prev : Tbl NL NR → Graph B NL → Graph B NR → Bool) (A : Tbl NL NR)
    {fs : Finset String} {md : {x // x ∈ fs} → SlotMode B} :
    (w : Fin 2) → ((TOp.obj fs md w).Pos → Graph B NL) → Graph B NR → Bool
  | ⟨0, _⟩, _ => fun _ => true
  | ⟨1, _⟩, a => pairAt (sL := sL) (sR := sR) prev A (a (.inr ⟨0, Nat.one_pos⟩))

variable (sL sR)

/-- **One row per operation of the left operand**, with `prev` as the walk at the next fuel. -/
def rowG (prev : Tbl NL NR → Graph B NL → Graph B NR → Bool) (A : Tbl NL NR) :
    Graph B NL → Graph B NR → Bool
  | .leaf j, y => prev A (sL j) y
  | .node .never _, _ => true
  | x@(.node (.held _ _ _) _), y => rightC sR (prev A x) (fun _ => false) y
  | x@(.node (.legacy _) _), y => rightC sR (prev A x) (fun _ => false) y
  | x@(.node .opaq _), y => rightC sR (prev A x) (fun _ => false) y
  | .node (.refine _ _) a, y => rowG prev A (a ()) y
  | .node (.union m) a, y => (List.finRange m).all fun p => rowG prev A (a p) y
  | x@(.node (.prim g) _), y => rightC sR (prev A x) (famPrimG g) y
  | x@(.node .set a), y => rightC sR (prev A x) (famSetG (prev [] (a ()))) y
  | x@(.node (.list _ _ _) a), y =>
      rightC sR (prev A x) (famListG ((listParts a).1.map (pairAt (sL := sL) (sR := sR) prev A))
        ((listParts a).2.1.map (pairAt (sL := sL) (sR := sR) prev A))
        ((listParts a).2.2.map (pairAt (sL := sL) (sR := sR) prev A))) y
  | x@(.node (.obj _ md s) a), y =>
      rightC sR (prev A x) (famObjG (md := md)
        (fun k => pairAt (sL := sL) (sR := sR) prev A (a (.inl k)))
        (blockTest (sL := sL) (sR := sR) (md := md) prev A s a)) y

/-- **The fuel of a walk over two closed codecs** of `NL` and `NR` entries. -/
def fuel (NL NR : Nat) : Nat := (NL * NR + 1) * (NL + NR + 2)

/-- **The walk at a fuel.** Each unfolding of an entry and each pair below a guard spends one. -/
def decG : Nat → Tbl NL NR → Graph B NL → Graph B NR → Bool
  | 0 => fun _ _ _ => false
  | n + 1 => rowG sL sR (decG n)

end Rows

/-! ## The views -/

section View
variable [Mean B] {N : Nat} (sys : Fin N → Graph B N) (o : Orient)

/-- The view of a slot mode: a `fill` holds the name at the caller side, and may lack it at the
    stored side. -/
def SlotMode.view : SlotMode B → SlotMode B
  | .fill _ => bif o.c then .opt else .req
  | m => m

/-- **The view of a graph term at an orientation**: each `held` becomes its term at the caller side
    of the orientation, an older reader reads every attribute, and a refinement over a term with an
    adapter keeps only the predicate of the caller side. An entry stays an entry. -/
def viewG : Graph B N → Graph B N
  | .leaf j => .leaf j
  | .node (.held s _ _) a => bif s == o.c then viewG (a false) else viewG (a true)
  | .node (.legacy _) a => bif o.c then .node .opaq (fun p => nomatch p) else viewG (a ())
  | .node (.refine p pA) a =>
      if belowTop sys (a ()) then .node (.refine p pA) fun _ => viewG (a ())
      else .node (.refine (bif o.c then Mean.truth false else p) (bif o.c then pA else Mean.truth true))
        fun _ => viewG (a ())
  | .node (.obj fs md s) a => .node (.obj fs (fun x => SlotMode.view o (md x)) s) fun p => viewG (a p)
  | .node op a => .node op fun p => viewG (a p)

/-- The view of each entry of a system. -/
def viewSys : Fin N → Graph B N := fun i => viewG sys o (sys i)

end View

/-- **Whether two closed codecs share no value**, at their roots. The fuel covers each pair of
    entries below a guard, and each unguarded unfolding between two guards. -/
def disjoint [Leaf B] {NL NR : Nat} (dL : Closed B NL) (rL : Fin NL) (dR : Closed B NR)
    (rR : Fin NR) : Bool :=
  decG dL.graph dR.graph (fuel NL NR) [] (.leaf rL) (.leaf rR)

/-- **Whether the two pairs of views are disjoint**: the views at the host share no value, and the
    views at the dual share no attribute. -/
def viewsDisjoint [Mean B] [Leaf B] {NL NR : Nat} (dL : Closed B NL) (rL : Fin NL) (dR : Closed B NR)
    (rR : Fin NR) : Bool :=
  decG (viewSys dL.graph .host) (viewSys dR.graph .host) (fuel NL NR) []
      (.leaf rL) (.leaf rR) &&
    decG (viewSys dL.graph .dual) (viewSys dR.graph .dual) (fuel NL NR) []
      (.leaf rL) (.leaf rR)

end Calculus.Alg.Scoped

namespace Calculus.Alg.Scoped

/-! ## Rows of positions, apart -/

section RowsGen
variable {X Y V : Type} (P : X → V → Bool) (Q : Y → V → Bool)

/-- A test is sound for a position where every partner it accepts shares no datum. -/
def SoundG (x : X) (f : Y → Bool) : Prop := ∀ y, f y = true → ∀ u, (P x u && Q y u) = false

/-- Two rows share no row of data. -/
def RowsAp (r₁ : List X) (r₂ : List Y) : Prop :=
  ∀ ws : List V, (zipP (r₁.map P) ws && zipP (r₂.map Q) ws) = false

variable {P Q}

/-- One sound test that accepts a position of two aligned rows keeps the two rows apart. -/
theorem rowsAp_of_anyZip : ∀ {r₁ : List X} {fs : List (Y → Bool)}, List.Forall₂ (SoundG P Q) r₁ fs →
    ∀ {r₂ : List Y}, anyZipG fs r₂ = true → RowsAp P Q r₁ r₂
  | _, _, .nil, _, h, _ => by simp [anyZipG] at h
  | t :: r₁, f :: fs, .cons ht hr, r₂, h, ws => by
      cases r₂ with
      | nil => simp [anyZipG] at h
      | cons u r₂ =>
        cases ws with
        | nil => simp [zipP]
        | cons w ws =>
          simp only [anyZipG, Bool.or_eq_true] at h
          simp only [List.map_cons, zipP]
          rcases h with h | h
          · exact apart_and_left (ht u h w)
          · exact apart_and_right (rowsAp_of_anyZip hr h ws)

/-- Two rows apart stay apart when two rows of equal length go behind them. -/
theorem RowsAp.append_left {A₁ X₁ : List X} {A₂ X₂ : List Y}
    (hA : A₁.length = A₂.length) (h : RowsAp P Q A₁ A₂) : RowsAp P Q (A₁ ++ X₁) (A₂ ++ X₂) := by
  intro ws
  rcases Nat.lt_or_ge ws.length A₁.length with hl | hl
  · rw [zipP_false_of_length_ne _ _ (by simp; omega), Bool.false_and]
  · rw [← List.take_append_drop A₁.length ws, List.map_append, List.map_append,
      zipP_append _ _ _ _ (by simp; omega), zipP_append _ _ _ _ (by simp; omega)]
    exact apart_and_left (h (ws.take A₁.length))

/-- Two rows apart stay apart when two rows of equal length go in front of them. -/
theorem RowsAp.append_right {B₁ X₁ : List X} {B₂ X₂ : List Y}
    (hX : X₁.length = X₂.length) (h : RowsAp P Q B₁ B₂) : RowsAp P Q (X₁ ++ B₁) (X₂ ++ B₂) := by
  intro ws
  rcases Nat.lt_or_ge ws.length X₁.length with hl | hl
  · rw [zipP_false_of_length_ne _ _ (by simp; omega), Bool.false_and]
  · rw [← List.take_append_drop X₁.length ws, List.map_append, List.map_append,
      zipP_append _ _ _ _ (by simp; omega), zipP_append _ _ _ _ (by simp; omega)]
    exact apart_and_right (h (ws.drop X₁.length))

/-- A disjoint position of two rows cut at one length lies in the first part or in the second part. -/
theorem anyZipG_take_drop : ∀ (n : Nat) {fs : List (Y → Bool)} {us : List Y},
    anyZipG fs us = true →
      anyZipG (fs.take n) (us.take n) = true ∨ anyZipG (fs.drop n) (us.drop n) = true
  | 0, _, _, h => Or.inr (by simpa using h)
  | _ + 1, [], _, h => by simp [anyZipG] at h
  | _ + 1, _ :: _, [], h => by simp [anyZipG] at h
  | n + 1, f :: fs, u :: us, h => by
      simp only [anyZipG, Bool.or_eq_true] at h
      rcases h with h | h
      · exact Or.inl (by simp [anyZipG, h])
      · rcases anyZipG_take_drop n h with h' | h'
        · exact Or.inl (by simp [anyZipG, h'])
        · exact Or.inr (by simpa using h')

/-- A row that a list shape assigns has a length of at least the prefix and the suffix. -/
theorem rowOfG_isSome_len' {α : Type} {pre suf : List α} {sp : Option α} {n : Nat} {r : List α}
    (h : rowOfG pre sp suf n = some r) : pre.length + suf.length ≤ n := by
  cases sp with
  | none =>
    rw [rowOfG_none_eq] at h
    split at h
    · omega
    · exact nomatch h
  | some c =>
    rw [rowOfG_some_eq] at h
    split at h
    · exact nomatch h
    · omega

/-- **Two list shapes apart at each common length**, where the row of the shapes finds one
    disjoint position. -/
theorem listRowG_sound {pre suf : List X} {sp : Option X} {fpre fsuf : List (Y → Bool)}
    {fsp : Option (Y → Bool)} (hp : List.Forall₂ (SoundG P Q) pre fpre)
    (hs : (sp = none ∧ fsp = none) ∨ ∃ t f, sp = some t ∧ fsp = some f ∧ SoundG P Q t f)
    (hf : List.Forall₂ (SoundG P Q) suf fsuf) {pre₂ suf₂ : List Y} {sp₂ : Option Y}
    (h : listRowG fpre fsp fsuf pre₂ sp₂ suf₂ = true) :
    ∀ n r₁ r₂, rowOfG pre sp suf n = some r₁ → rowOfG pre₂ sp₂ suf₂ n = some r₂ →
      RowsAp P Q r₁ r₂ := by
  have hlp := hp.length_eq
  have hlf := hf.length_eq
  intro n r₁ r₂ h₁ h₂
  rcases hs with ⟨rfl, rfl⟩ | ⟨t, f, rfl, rfl, htf⟩
  · simp only [listRowG] at h
    rw [rowOfG_none_eq] at h₁
    split at h₁
    · next hn =>
      simp only [Option.some.injEq] at h₁; subst h₁
      rw [show fpre.length + fsuf.length = n by omega, h₂] at h
      exact rowsAp_of_anyZip (forall₂_append hp hf) h
    · exact nomatch h₁
  · cases sp₂ with
    | none =>
      simp only [listRowG] at h
      rw [rowOfG_none_eq] at h₂
      split at h₂
      · next hn =>
        simp only [Option.some.injEq] at h₂; subst h₂
        subst hn
        cases hfs : rowOfG fpre (some f) fsuf (pre₂.length + suf₂.length) with
        | none =>
          have := rowOfG_isSome_len' h₁
          rw [rowOfG_some_eq, if_neg (by omega)] at hfs
          exact nomatch hfs
        | some fs =>
          rw [hfs] at h
          have hF := rowOfG_forall₂ (R := SoundG P Q) hp (Or.inr ⟨t, f, rfl, rfl, htf⟩) hf h₁ hfs
          exact rowsAp_of_anyZip hF h
      · exact nomatch h₂
    | some c =>
      simp only [listRowG] at h
      split at h
      · next hdom =>
        have hdm := dominates_max hdom
        have hn₁ := rowOfG_isSome_len' h₁
        have hn₂ := rowOfG_isSome_len' h₂
        generalize hP : max fpre.length pre₂.length = P' at h hdm
        generalize hS : max fsuf.length suf₂.length = S' at h hdm
        split at h
        · next fs us hfs hus =>
          obtain ⟨rN, hrN⟩ := rowOfG_total (pre := pre) (suf := suf) (c := t) (n := P' + S')
            (by omega)
          have hF := rowOfG_forall₂ (R := SoundG P Q) hp (Or.inr ⟨t, f, rfl, rfl, htf⟩) hf hrN hfs
          have hr₁ := rowOfG_respread (P := P') (S := S') (n := n) (by omega) (by omega)
            (by omega) hrN h₁
          have hr₂ := rowOfG_respread (P := P') (S := S') (n := n) (by omega) (by omega)
            (by omega) hus h₂
          have hlN := rowOfG_length hrN
          have hlu := rowOfG_length hus
          have hlf' := hF.length_eq
          subst hr₁ hr₂
          rcases anyZipG_take_drop P' h with ha | ha
          · rw [List.append_assoc, List.append_assoc]
            exact RowsAp.append_left (by simp; omega)
              (rowsAp_of_anyZip (List.forall₂_take P' hF) ha)
          · exact RowsAp.append_right (by simp; omega)
              (rowsAp_of_anyZip (List.forall₂_drop P' hF) ha)
        · exact nomatch h
      · exact nomatch h

end RowsGen

/-! ## Soundness -/

section Sound
variable {S : Syn} [Sem S] (τ : (s : Bool) → TableAt S.sig s) (o : Orient)

/-- **A graph system with a meaning**: a flat system over the term container, a fixed point of the
    system at the maps, and no cycle of unguarded edges. A closed codec gives one, and so does the
    view of a closed codec. -/
structure GSys (N : Nat) where
  sys : Fin N → Graph S.sig N
  e : Fin N → Mean.C S.sig
  fix : IsFix (sysB (TStep τ) sys) e
  noCycle : ¬ Cycle (TSig S.sig) sys

/-- The meaning of a graph term of a system: the term at the fixed point of the system. -/
def mng {N : Nat} (d : GSys τ N) (t : Graph S.sig N) : Mean.C S.sig :=
  t.interp (TStep τ) d.e

/-- **The graph system of a closed codec**: its graph, the solution of its scope, and the order of
    its entries. -/
def Closed.toG {N : Nat} (d : Closed S.sig N) : GSys τ N where
  sys := d.graph
  e := d.sol (TStep τ) Mean.d
  fix := (scope_solution Mean.d_pos (TStep_lawful τ) d).1
  noCycle := noCycle_of_rank (fun i => i.val) (SSys.order d).1

/-- **A step-indexed relation** between two codecs: true at the depth zero, closed downward, and
    read through the maps only. -/
structure StepRel (S : Syn) [Sem S] where
  R : Nat → Mean.C S.sig → Mean.C S.sig → Prop
  zero : ∀ c c', R 0 c c'
  mono : ∀ {k k' c c'}, k' ≤ k → R k c c' → R k' c c'
  congr : ∀ {k c c' c₁ c₁'}, c.f = c₁.f → c'.f = c₁'.f → R k c c' → R k c₁ c₁'

/-- **Apart below a depth**: no datum of a smaller depth is accepted by both codecs at the
    orientation. -/
def AB (k : Nat) (c c' : Mean.C S.sig) : Prop :=
  ∀ v, Mean.d (B := S.sig) v < k → ((c.f o v).isSome && (c'.f o v).isSome) = false

variable {τ o}

/-- Apartness below a depth reads the two codecs through their maps only. -/
theorem AB.congr {k : Nat} {c c' c₁ c₁' : Mean.C S.sig} (h₁ : c.f = c₁.f) (h₂ : c'.f = c₁'.f)
    (h : AB o k c c') : AB o k c₁ c₁' := fun v hv => by rw [← h₁, ← h₂]; exact h v hv

/-- Apartness below a depth holds below each smaller depth. -/
theorem AB.mono {k k' : Nat} {c c' : Mean.C S.sig} (hk : k' ≤ k) (h : AB o k c c') :
    AB o k' c c' := fun v hv => h v (by omega)

/-- Any two codecs are apart below the depth zero. -/
theorem AB.zero (c c' : Mean.C S.sig) : AB o 0 c c' := fun _ hv => absurd hv (Nat.not_lt_zero _)

variable (o) in
/-- Apartness below a depth is a step-indexed relation. -/
def AB.rel : StepRel S := ⟨AB o, AB.zero, AB.mono, AB.congr⟩

/-- A codec that accepts no datum is apart from each codec. -/
theorem AB.of_left {k : Nat} {c c' : Mean.C S.sig} (h : ∀ v, (c.f o v).isSome = false) :
    AB o k c c' := fun v _ => by rw [h v, Bool.false_and]

/-- Each codec is apart from a codec that accepts no datum. -/
theorem AB.of_right {k : Nat} {c c' : Mean.C S.sig} (h : ∀ v, (c'.f o v).isSome = false) :
    AB o k c c' := fun v _ => by rw [h v, Bool.and_false]

/-- Apart at every depth is apart. -/
theorem apart_of_AB {c c' : Mean.C S.sig} (h : ∀ k, AB o (k + 1) c c') :
    ∀ v, ((c.f o v).isSome && (c'.f o v).isSome) = false :=
  fun v => h (Mean.d (B := S.sig) v) v (Nat.lt_succ_self _)

/-- **An entry is its body**, at the maps: the solution is a fixed point of the system. -/
theorem mng_leaf {N : Nat} (d : GSys τ N) (i : Fin N) :
    (mng τ d (.leaf i)).f = (mng τ d (d.sys i)).f :=
  d.fix i

/-- A gate that answers `true` has a map that sends the input. -/
theorem gate_isSome {X Y : Type} {m : X → Option Y} {q : Y → Bool} {x : X}
    (h : gate m q x = true) : (m x).isSome = true := by
  unfold gate at h
  cases hm : m x with
  | none => rw [hm] at h; exact nomatch h
  | some _ => rfl

/-- A refinement accepts only what its inner codec accepts. -/
theorem refine2_acc {c : Mean.C S.sig} {qV qA : Mean.V (B := S.sig) → Bool} {v : Mean.V (B := S.sig)}
    (h : ((refine2 c qV qA).f o v).isSome = true) : (c.f o v).isSome = true := by
  rw [refine2_f_isSome, Bool.and_eq_true] at h
  exact gate_isSome h.2

/-- A union accepts what one of its options accepts. -/
theorem union_acc {m : Nat} {a : Fin m → Mean.C S.sig} {μ : Option (Mean.Mem (B := S.sig))}
    {v : Mean.V (B := S.sig)} (h : ((altCodec (List.ofFn a) μ).f o v).isSome = true) :
    ∃ p, ((a p).f o v).isSome = true := by
  obtain ⟨c, hc, hv⟩ := (select_isSome_attempt _ _ _).mp h
  obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hc
  exact ⟨p, hv⟩

/-- A codec apart from an inner codec is apart from each refinement of the inner codec. -/
theorem AB.refine_right {k : Nat} {X c : Mean.C S.sig} {qV qA : Mean.V (B := S.sig) → Bool}
    (h : AB o k X c) : AB o k X (refine2 c qV qA) := fun v hv => by
  cases hy : ((refine2 c qV qA).f o v).isSome
  · rw [Bool.and_false]
  · have := h v hv; rw [refine2_acc hy] at this; rw [Bool.and_true]; simpa using this

/-- A refinement of a codec is apart from each codec that the codec is apart from. -/
theorem AB.refine_left {k : Nat} {X c : Mean.C S.sig} {qV qA : Mean.V (B := S.sig) → Bool}
    (h : AB o k c X) : AB o k (refine2 c qV qA) X := fun v hv => by
  cases hy : ((refine2 c qV qA).f o v).isSome
  · rw [Bool.false_and]
  · have := h v hv; rw [refine2_acc hy] at this; rw [Bool.true_and]; simpa using this

/-- A codec apart from each option is apart from the union of the options. -/
theorem AB.union_right {k m : Nat} {X : Mean.C S.sig} {a : Fin m → Mean.C S.sig}
    {μ : Option (Mean.Mem (B := S.sig))} (h : ∀ p, AB o k X (a p)) :
    AB o k X (altCodec (List.ofFn a) μ) := fun v hv => by
  cases hy : ((altCodec (List.ofFn a) μ).f o v).isSome
  · rw [Bool.and_false]
  · obtain ⟨p, hp⟩ := union_acc hy
    have := h p v hv; rw [hp] at this; rw [Bool.and_true]; simpa using this

/-- The union of options is apart from each codec that each option is apart from. -/
theorem AB.union_left {k m : Nat} {X : Mean.C S.sig} {a : Fin m → Mean.C S.sig}
    {μ : Option (Mean.Mem (B := S.sig))} (h : ∀ p, AB o k (a p) X) :
    AB o k (altCodec (List.ofFn a) μ) X := fun v hv => by
  cases hy : ((altCodec (List.ofFn a) μ).f o v).isSome
  · rw [Bool.false_and]
  · obtain ⟨p, hp⟩ := union_acc hy
    have := h p v hv; rw [hp] at this; rw [Bool.true_and]; simpa using this

variable {N NR : Nat}

/-- **The rows of the right operand are sound** for a step-indexed relation that the bottom, a
    refinement and a union keep on the right, for a left codec that \`restart\` and \`fam\` are sound
    for. -/
theorem StepRel.of_rightC (Q : StepRel S) (d : GSys τ N) {X : Mean.C S.sig} {k : Nat}
    {restart fam : Graph S.sig N → Bool}
    (hn : ∀ a, Q.R k X (mng τ d (.node .never a)))
    (hq : ∀ q qA a, Q.R k X (mng τ d (a ())) → Q.R k X (mng τ d (.node (.refine q qA) a)))
    (hu : ∀ m a, (∀ p, Q.R k X (mng τ d (a p))) → Q.R k X (mng τ d (.node (.union m) a)))
    (hr : ∀ y, restart y = true → Q.R k X (mng τ d y))
    (hf : ∀ y, fam y = true → Q.R k X (mng τ d y)) :
    ∀ y, rightC d.sys restart fam y = true → Q.R k X (mng τ d y) := by
  intro y
  induction y with
  | leaf j =>
    intro h
    simp only [rightC, Bool.or_eq_true] at h
    exact h.elim (hf _) fun h => Q.congr rfl (mng_leaf d j).symm (hr _ h)
  | node op a ih =>
    intro h
    cases op with
    | never => exact hn a
    | refine q qA =>
      simp only [rightC, Bool.or_eq_true] at h
      exact h.elim (hf _) fun h => hq q qA a (ih () h)
    | union m =>
      simp only [rightC, Bool.or_eq_true, List.all_eq_true, List.mem_finRange, true_implies] at h
      exact h.elim (hf _) fun h => hu m a fun p => ih p (h p)
    | prim _ | opaq | set | list _ _ _ | held _ _ _ | legacy _ | obj _ _ _ => exact hf _ h

/-- **The rows of the right operand are sound** for apartness. -/
theorem AB.of_rightC (d : GSys τ N) {X : Mean.C S.sig} {k : Nat}
    {restart fam : Graph S.sig N → Bool}
    (hr : ∀ y, restart y = true → AB o k X (mng τ d y))
    (hf : ∀ y, fam y = true → AB o k X (mng τ d y)) :
    ∀ y, rightC d.sys restart fam y = true → AB o k X (mng τ d y) :=
  StepRel.of_rightC (AB.rel o) d (fun _ => AB.of_right fun _ => rfl)
    (fun _ _ _ h => AB.refine_right h) (fun _ _ h => AB.union_right h) hr hf

/-! ### The shape classes -/

/-- The former class of an operation, where the operation is a former or a primitive. -/
def TOp.cls {B : Sig} : TOp B → Option Former
  | .prim _ => some .prim
  | .set => some .set
  | .list _ _ _ => some .list
  | .obj _ _ _ => some .object
  | _ => none

/-- **An operation of a class accepts only data of that class.** -/
theorem former_of_run [Shapes S] {op : TOp S.sig} {c : Former} (hc : op.cls = some c)
    (a : op.Pos → Mean.C S.sig) {v : Mean.V (B := S.sig)}
    (h : ((TOp.run τ op a).f o v).isSome = true) : Shapes.former v = c := by
  cases op with
  | prim g =>
    obtain rfl : c = .prim := (Option.some.inj hc).symm
    exact Shapes.prim o g v h
  | set =>
    obtain rfl : c = .set := (Option.some.inj hc).symm
    simp only [TOp.run] at h
    split at h
    · next L hL => exact Shapes.set L hL _ o v h
    · exact nomatch h
  | list n s m =>
    obtain rfl : c = .list := (Option.some.inj hc).symm
    simp only [TOp.run] at h
    split at h
    · next L hL =>
      rw [listCodec_f] at h
      cases hx : L.p.out v with
      | none => rw [hx] at h; exact nomatch h
      | some xs =>
        rw [L.p.into_out hx]
        exact Shapes.list L hL xs
    · exact nomatch h
  | obj fs md w =>
    obtain rfl : c = .object := (Option.some.inj hc).symm
    simp only [TOp.run] at h
    split at h
    · next F hF =>
      rw [objectCodec_f] at h
      cases hx : F.p.out v with
      | none => rw [hx] at h; exact nomatch h
      | some m =>
        rw [F.p.into_out hx]
        exact Shapes.map F hF m
    · exact nomatch h
  | opaq => exact nomatch hc
  | never => exact nomatch hc
  | refine _ _ => exact nomatch hc
  | held _ _ _ => exact nomatch hc
  | legacy _ => exact nomatch hc
  | union _ => exact nomatch hc

/-- **Two operations of different classes are apart.** -/
theorem AB.of_cls [Shapes S] {k : Nat} {op op' : TOp S.sig} {c c' : Former} (hc : op.cls = some c)
    (hc' : op'.cls = some c') (hne : c ≠ c') (a : op.Pos → Mean.C S.sig)
    (b : op'.Pos → Mean.C S.sig) : AB o k (TOp.run τ op a) (TOp.run τ op' b) := fun v _ => by
  cases h1 : ((TOp.run τ op a).f o v).isSome
  · rfl
  · cases h2 : ((TOp.run τ op' b).f o v).isSome
    · rfl
    · exact absurd ((former_of_run hc a h1).symm.trans (former_of_run hc' b h2)) hne

/-- Two operations of different classes are apart, the right one a node of a graph. -/
theorem AB.of_cls_node [Shapes S] {k N : Nat} (d : GSys τ N) {op op' : TOp S.sig}
    {c c' : Former} (a : op.Pos → Mean.C S.sig) (b : op'.Pos → Graph S.sig N)
    (hc : op.cls = some c) (hc' : op'.cls = some c') (hne : c ≠ c') :
    AB o k (TOp.run τ op a) (mng τ d (.node op' b)) :=
  AB.of_cls hc hc' hne a fun p => mng τ d (b p)

variable (S o) in
/-- **The laws of a universe that the decision reads**, at one orientation, over codecs. -/
structure Laws [Leaf S.sig] : Prop where
  /-- Two primitives that the leaf keeps apart share no datum. -/
  prim : ∀ g g', Leaf.primsApart g g' = true → ∀ v,
    (((Mean.ground (B := S.sig) g).f o v).isSome && ((Mean.ground (B := S.sig) g').f o v).isSome) = false
  /-- Two sets whose elements share no datum share no set. -/
  set : ∀ L, Mean.set (B := S.sig) = some L → ∀ c c' : Mean.C S.sig,
    (∀ u, ((c.f o u).isSome && (c'.f o u).isSome) = false) →
      ∀ v, (((L.lift c).f o v).isSome && ((L.lift c').f o v).isSome) = false

/-! ### The families -/

variable [Leaf S.sig] [Shapes S]

/-- The family of a primitive accepts only a partner that shares no datum with the primitive. -/
theorem famPrimG_sound (laws : Laws S o) (d : GSys τ N) {k : Nat} {g : S.sig.Ground}
    (a : (TOp.prim g).Pos → Mean.C S.sig) :
    ∀ y, famPrimG g y = true → AB o k (TOp.run τ (.prim g) a) (mng τ d y)
  | .leaf _, h => nomatch h
  | .node op b, h => by
    cases op with
    | prim g' => exact fun v _ => laws.prim g g' h v
    | set => exact AB.of_cls_node (c := .prim) (c' := .set) (op' := .set) d a b rfl rfl (by decide)
    | list _ _ _ => exact AB.of_cls_node (c := .prim) (c' := .list) (op' := .list _ _ _) d a b rfl rfl (by decide)
    | obj _ _ _ => exact AB.of_cls_node (c := .prim) (c' := .object) (op' := .obj _ _ _) d a b rfl rfl (by decide)
    | opaq => exact nomatch h
    | never => exact nomatch h
    | refine _ _ => exact nomatch h
    | held _ _ _ => exact nomatch h
    | legacy _ => exact nomatch h
    | union _ => exact nomatch h

/-- The family of a set accepts only a partner that shares no datum with the set. -/
theorem famSetG_sound (laws : Laws S o) (d : GSys τ N) {k : Nat}
    (a : (TOp.set (B := S.sig)).Pos → Mean.C S.sig) {mt : Graph S.sig N → Bool}
    (hmt : ∀ e, mt e = true → ∀ v, (((a ()).f o v).isSome && ((mng τ d e).f o v).isSome) = false) :
    ∀ y, famSetG mt y = true → AB o k (TOp.run τ .set a) (mng τ d y)
  | .leaf _, h => nomatch h
  | .node op b, h => by
    cases op with
    | set =>
      intro v _
      show (((TOp.run τ .set a).f o v).isSome && ((TOp.run τ .set fun p => mng τ d (b p)).f o v).isSome) = false
      simp only [TOp.run]
      split
      · next L hL => exact laws.set L hL _ _ (hmt _ h) v
      · rfl
    | prim _ => exact AB.of_cls_node (c := .set) (c' := .prim) (op' := .prim _) d a b rfl rfl (by decide)
    | list _ _ _ => exact AB.of_cls_node (c := .set) (c' := .list) (op' := .list _ _ _) d a b rfl rfl (by decide)
    | obj _ _ _ => exact AB.of_cls_node (c := .set) (c' := .object) (op' := .obj _ _ _) d a b rfl rfl (by decide)
    | opaq => exact nomatch h
    | never => exact nomatch h
    | refine _ _ => exact nomatch h
    | held _ _ _ => exact nomatch h
    | legacy _ => exact nomatch h
    | union _ => exact nomatch h

/-! ### The walk -/

variable {NL : Nat} {dL : GSys τ NL} {dR : GSys τ NR}

variable (τ) in
/-- The assumed pairs hold the relation below the depth. -/
def Hyp (Q : StepRel S) (dL : GSys τ NL) (dR : GSys τ NR) (k : Nat) (A : Tbl NL NR) : Prop :=
  ∀ p ∈ A, Q.R k (mng τ dL (.leaf p.1)) (mng τ dR (.leaf p.2))

variable (τ) in
/-- A walk at the next fuel is sound for the relation. -/
def Prev (Q : StepRel S) (dL : GSys τ NL) (dR : GSys τ NR)
    (prev : Tbl NL NR → Graph S.sig NL → Graph S.sig NR → Bool) : Prop :=
  ∀ A x y, prev A x y = true → ∀ k, Hyp τ Q dL dR k A → Q.R (k + 1) (mng τ dL x) (mng τ dR y)

omit [Leaf S.sig] [Shapes S] in
/-- Assumed pairs that hold the relation below a depth hold the relation below each smaller depth. -/
theorem Hyp.mono {Q : StepRel S} {k k' : Nat} {A : Tbl NL NR} (hk : k' ≤ k)
    (h : Hyp τ Q dL dR k A) : Hyp τ Q dL dR k' A := fun p hp => Q.mono hk (h p hp)

omit [Leaf S.sig] [Shapes S] in
/-- **A pair below a guard holds the relation below the depth**, by the Löb step. An assumption at
    the index k gives a result at the index k + 1. A new pair holds at each smaller depth, by
    induction on the depth, because the walk assumes the new pair only at a smaller depth. The
    depth falls only at a row that goes one level down into the datum. -/
theorem pairAt_soundR {Q : StepRel S} {prev : Tbl NL NR → Graph S.sig NL → Graph S.sig NR → Bool}
    (hp : Prev τ Q dL dR prev) :
    ∀ a b A k, pairAt (sL := dL.sys) (sR := dR.sys) prev A a b = true → Hyp τ Q dL dR k A →
      Q.R k (mng τ dL a) (mng τ dR b)
  | .leaf i, .leaf j, A, k, h, hA => by
    simp only [pairAt, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨⟨i', j'⟩, hp', hpe⟩ := List.any_eq_true.mp h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hpe
      obtain ⟨rfl, rfl⟩ := hpe
      exact hA _ hp'
    · have key : ∀ m, m ≤ k → Q.R m (mng τ dL (.leaf i)) (mng τ dR (.leaf j)) := by
        intro m
        induction m with
        | zero => exact fun _ => Q.zero _ _
        | succ m ih =>
          intro hm
          have hA' : Hyp τ Q dL dR m ((i, j) :: A) := by
            intro p hp'
            rcases List.mem_cons.mp hp' with rfl | hp'
            · exact ih (by omega)
            · exact Q.mono (by omega) (hA p hp')
          exact Q.congr (mng_leaf dL i).symm (mng_leaf dR j).symm (hp _ _ _ h m hA')
      exact key k (Nat.le_refl k)
  | .leaf _, .node _ _, A, k, h, hA | .node _ _, .leaf _, A, k, h, hA
  | .node _ _, .node _ _, A, k, h, hA => by
    cases k with
    | zero => exact Q.zero _ _
    | succ k => exact hp A _ _ h k (hA.mono (by omega))

/-! ### The list row -/

omit [Leaf S.sig] [Shapes S] in
/-- The slots of a prefix and a spread are the row that the shape with no suffix assigns. -/
theorem slots_eq_rowOfG {V M : Type} : ∀ (pre : List (Codec V M)) (sp : Option (Codec V M)) (m : Nat),
    slots pre sp m = rowOfG pre sp [] m
  | [], none, 0 => rfl
  | [], none, _ + 1 => rfl
  | [], some c, 0 => rfl
  | [], some c, m + 1 => by
      rw [slots, slots_eq_rowOfG [] (some c) m]
      simp only [rowOfG, List.length_nil, List.append_nil, List.nil_append, Nat.add_zero]
      rw [if_neg (by omega), if_neg (by omega)]
      simp [List.replicate_succ]
  | _ :: _, none, 0 => rfl
  | _ :: _, some _, 0 => rfl
  | c :: cs, sp, m + 1 => by
      rw [slots, slots_eq_rowOfG cs sp m]
      cases sp with
      | none =>
        simp only [rowOfG, List.length_cons, List.length_nil, List.append_nil, Nat.add_zero]
        rcases Nat.decEq m cs.length with h | h
        · rw [if_neg h, if_neg (by omega)]; rfl
        · rw [if_pos h, if_pos (by omega)]; rfl
      | some d =>
        simp only [rowOfG, List.length_cons, List.length_nil, List.append_nil, Nat.add_zero]
        rcases Nat.lt_or_ge m cs.length with h | h
        · rw [if_pos h, if_pos (by omega)]; rfl
        · rw [if_neg (by omega), if_neg (by omega)]
          simp only [Option.map_some, List.cons_append, Option.some.injEq, List.cons.injEq, true_and]
          congr 2
          omega

/-- The row of `slotsL` is the row of the shape. -/
theorem slotsL_eq_rowOfG {V M : Type} (pre : List (Codec V M)) (sp : Option (Codec V M))
    (suf : List (Codec V M)) (n : Nat) : slotsL pre sp suf n = rowOfG pre sp suf n := by
  unfold slotsL
  rw [slots_eq_rowOfG]
  cases sp with
  | none =>
    simp only [rowOfG, List.length_nil, Nat.add_zero, List.append_nil]
    split
    · rw [if_neg (by omega)]
    · split
      · next h => rw [if_pos (by omega)]; rfl
      · next h => rw [if_neg (by omega)]; rfl
  | some c =>
    simp only [rowOfG, List.length_nil, Nat.add_zero, List.append_nil]
    split
    · rw [if_pos (by omega)]
    · split
      · next h => rw [if_pos (by omega)]; rfl
      · next h =>
        rw [if_neg (by omega)]
        simp only [Option.map_some, List.append_assoc, Option.some.injEq]
        rw [show n - suf.length - pre.length - 0 = n - pre.length - suf.length by omega]

omit [Leaf S.sig] [Shapes S] in
/-- A traversal of a zip that succeeds accepts each position. -/
theorem zipP_of_traverse {V M : Type} {o : Orient} :
    ∀ (row : List (Codec V M)) (xs : List V), row.length = xs.length →
      (traverse (fun cx : Codec V M × V => cx.1.f o cx.2) (row.zip xs)).isSome = true →
        zipP (row.map fun c u => (c.f o u).isSome) xs = true
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => nomatch h
  | _ :: _, [], h, _ => nomatch h
  | c :: cs, x :: xs, h, ht => by
      rw [List.zip_cons_cons, traverse_cons_isSome, Bool.and_eq_true] at ht
      simp only [List.map_cons, zipP, Bool.and_eq_true]
      exact ⟨ht.1, zipP_of_traverse cs xs (by simpa using h) ht.2⟩

omit [Leaf S.sig] [Shapes S] in
/-- A row of data accepted position for position, each datum of a smaller depth. -/
theorem zipP_depth {V M : Type} {o : Orient} {D : V → Bool} :
    ∀ (row : List (Codec V M)) (xs : List V), (∀ u ∈ xs, D u = true) →
      zipP (row.map fun c u => (c.f o u).isSome) xs = true →
        zipP (row.map fun c u => D u && (c.f o u).isSome) xs = true
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => nomatch h
  | _ :: _, [], _, h => nomatch h
  | c :: cs, x :: xs, hD, h => by
      simp only [List.map_cons, zipP, Bool.and_eq_true] at h ⊢
      exact ⟨⟨hD x List.mem_cons_self, h.1⟩,
        zipP_depth cs xs (fun u hu => hD u (List.mem_cons_of_mem _ hu)) h.2⟩

omit [Leaf S.sig] [Shapes S] in
/-- **A list codec accepts a datum through the row of its shape**, each element of a smaller
    depth. -/
theorem list_acc (L : ListA (Mean.V (B := S.sig)) (Mean.Mem (B := S.sig)) Mean.mem Mean.d)
    {pre suf : List (Mean.C S.sig)} {sp : Option (Mean.C S.sig)} {v : Mean.V (B := S.sig)} {k : Nat}
    (h : ((listCodec L.toSummand pre sp suf).f o v).isSome = true) (hv : Mean.d (B := S.sig) v < k + 1) :
    ∃ xs, L.p.out v = some xs ∧ ∃ row, rowOfG pre sp suf xs.length = some row ∧
      zipP (row.map fun c u => decide (Mean.d (B := S.sig) u < k) && (c.f o u).isSome) xs = true := by
  rw [listCodec_f] at h
  cases hx : L.p.out v with
  | none => rw [hx] at h; exact nomatch h
  | some xs =>
    rw [hx] at h
    simp only [Option.bind_some, Option.isSome_map] at h
    refine ⟨xs, rfl, ?_⟩
    unfold alignL at h
    cases hs : slotsL pre sp suf xs.length with
    | none => rw [hs] at h; exact nomatch h
    | some row =>
      rw [hs] at h
      simp only [Option.map_some, Option.bind_some] at h
      refine ⟨row, by rw [← slotsL_eq_rowOfG]; exact hs, ?_⟩
      have hvx := L.p.into_out hx
      refine zipP_depth row xs (fun u hu => ?_) (zipP_of_traverse row xs (slotsL_length _ _ _ _ _ hs) h)
      have := L.d_lt xs u hu
      rw [← hvx] at this
      exact decide_eq_true (by omega)

omit [Leaf S.sig] [Shapes S] in
/-- A map inside a count of zero or one is the map of the result. -/
theorem optOf_map {X Y : Type} (g : X → Y) : ∀ (s : Fin 2) (f : Fin s → X),
    optOf s (fun p => g (f p)) = (optOf s f).map g
  | ⟨0, _⟩, _ => rfl
  | ⟨1, _⟩, _ => rfl

omit [Leaf S.sig] [Shapes S] in
/-- A relation that holds between each element and its image holds between a list and its map. -/
theorem forall₂_map_self {X Y : Type} {R : X → Y → Prop} {f : X → Y} :
    ∀ l : List X, (∀ t ∈ l, R t (f t)) → List.Forall₂ R l (l.map f)
  | [], _ => .nil
  | t :: l, h => .cons (h t List.mem_cons_self) (forall₂_map_self l fun t' ht => h t' (List.mem_cons_of_mem _ ht))

omit [Leaf S.sig] [Shapes S] in
/-- An optional term and its optional test are both absent, or both present and related. -/
theorem optCases {X Y : Type} {R : X → Y → Prop} {f : X → Y} (sp : Option X) (h : ∀ t, R t (f t)) :
    (sp = none ∧ sp.map f = none) ∨ ∃ t g, sp = some t ∧ sp.map f = some g ∧ R t g := by
  cases sp with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some t => exact Or.inr ⟨t, f t, rfl, rfl, h t⟩

omit [Leaf S.sig] [Shapes S] in
/-- The list codec of a list node of a graph, over the meanings of its positions. -/
theorem mng_list {N : Nat} (d : GSys τ N) {n m : Nat} {s' : Fin 2}
    (a : (TOp.list n s' m (B := S.sig)).Pos → Graph S.sig N) :
    mng τ d (.node (.list n s' m) a) = TOp.run τ (.list n s' m) (fun p => mng τ d (a p)) := rfl

omit [Leaf S.sig] [Shapes S] in
/-- The codec row of a list node is the map of the term row through the meaning. -/
theorem rowOfG_listParts {N : Nat} (d : GSys τ N) {n m : Nat} {s' : Fin 2}
    (a : (TOp.list n s' m (B := S.sig)).Pos → Graph S.sig N) (len : Nat) :
    rowOfG (List.ofFn fun p => mng τ d (a (.inl p))) (optOf s' fun p => mng τ d (a (.inr (.inl p))))
        (List.ofFn fun p => mng τ d (a (.inr (.inr p)))) len =
      (rowOfG (listParts a).1 (listParts a).2.1 (listParts a).2.2 len).map (List.map (mng τ d)) := by
  rw [← rowOfG_map]
  simp only [listParts, List.map_ofFn, ← optOf_map]
  rfl

omit [Leaf S.sig] in
/-- **The list row is sound.** -/
theorem listRow_sound {prev : Tbl NL NR → Graph S.sig NL → Graph S.sig NR → Bool}
    (hp : Prev τ (AB.rel o) dL dR prev) {n₁ m₁ : Nat} {s₁' : Fin 2}
    (a : (TOp.list n₁ s₁' m₁ (B := S.sig)).Pos → Graph S.sig NL) {A : Tbl NL NR} {k : Nat}
    (hA : Hyp τ (AB.rel o) dL dR k A) (y : Graph S.sig NR)
    (h : famListG ((listParts a).1.map (pairAt (sL := dL.sys) (sR := dR.sys) prev A))
        ((listParts a).2.1.map (pairAt (sL := dL.sys) (sR := dR.sys) prev A))
        ((listParts a).2.2.map (pairAt (sL := dL.sys) (sR := dR.sys) prev A)) y = true) :
    AB o (k + 1) (mng τ dL (.node (.list n₁ s₁' m₁) a)) (mng τ dR y) := by
  cases y with
  | leaf _ => exact nomatch h
  | node op b =>
    cases op with
    | prim _ => exact AB.of_cls_node (op := .list n₁ s₁' m₁) (c := .list) (c' := .prim) (op' := .prim _) dR (fun p => mng τ dL (a p)) b rfl rfl (by decide)
    | set => exact AB.of_cls_node (op := .list n₁ s₁' m₁) (c := .list) (c' := .set) (op' := .set) dR (fun p => mng τ dL (a p)) b rfl rfl (by decide)
    | obj _ _ _ => exact AB.of_cls_node (op := .list n₁ s₁' m₁) (c := .list) (c' := .object) (op' := .obj _ _ _) dR (fun p => mng τ dL (a p)) b rfl rfl (by decide)
    | opaq => exact nomatch h
    | never => exact nomatch h
    | refine _ _ => exact nomatch h
    | held _ _ _ => exact nomatch h
    | legacy _ => exact nomatch h
    | union _ => exact nomatch h
    | list n₂ s₂' m₂ =>
      let P : Graph S.sig NL → Mean.V (B := S.sig) → Bool := fun t u =>
        decide (Mean.d (B := S.sig) u < k) && ((mng τ dL t).f o u).isSome
      let Q : Graph S.sig NR → Mean.V (B := S.sig) → Bool := fun t u =>
        decide (Mean.d (B := S.sig) u < k) && ((mng τ dR t).f o u).isSome
      have hsnd : ∀ t, SoundG P Q t (pairAt (sL := dL.sys) (sR := dR.sys) prev A t) := by
        intro t y' hy u
        have hab := pairAt_soundR hp t y' A k hy hA
        simp only [P, Q]
        cases hd : decide (Mean.d (B := S.sig) u < k)
        · rfl
        · simp only [Bool.true_and]
          exact hab u (of_decide_eq_true hd)
      have hrows := listRowG_sound (P := P) (Q := Q)
        (forall₂_map_self _ fun t _ => hsnd t)
        (optCases _ hsnd)
        (forall₂_map_self _ fun t _ => hsnd t) h
      intro v hv
      show (((TOp.run τ (.list n₁ s₁' m₁) fun p => mng τ dL (a p)).f o v).isSome &&
        ((TOp.run τ (.list n₂ s₂' m₂) fun p => mng τ dR (b p)).f o v).isSome) = false
      simp only [TOp.run]
      split
      · next L hL =>
        cases h1 : ((listCodec L.toSummand (List.ofFn fun p => mng τ dL (a (.inl p)))
            (optOf s₁' fun p => mng τ dL (a (.inr (.inl p))))
            (List.ofFn fun p => mng τ dL (a (.inr (.inr p))))).f o v).isSome
        · rfl
        cases h2 : ((listCodec L.toSummand (List.ofFn fun p => mng τ dR (b (.inl p)))
            (optOf s₂' fun p => mng τ dR (b (.inr (.inl p))))
            (List.ofFn fun p => mng τ dR (b (.inr (.inr p))))).f o v).isSome
        · rfl
        obtain ⟨xs, hx, r₁, hr₁, hz₁⟩ := list_acc L h1 hv
        obtain ⟨xs', hx', r₂, hr₂, hz₂⟩ := list_acc L h2 hv
        rw [hx] at hx'
        cases hx'
        rw [rowOfG_listParts dL a] at hr₁
        erw [rowOfG_listParts dR b] at hr₂
        cases hT₁ : rowOfG (listParts a).1 (listParts a).2.1 (listParts a).2.2 xs.length with
        | none => rw [hT₁] at hr₁; exact nomatch hr₁
        | some t₁ =>
          cases hT₂ : rowOfG (listParts b).1 (listParts b).2.1 (listParts b).2.2 xs.length with
          | none => rw [hT₂] at hr₂; exact nomatch hr₂
          | some t₂ =>
            rw [hT₁] at hr₁
            rw [hT₂] at hr₂
            obtain rfl := (Option.some.inj hr₁).symm
            obtain rfl := (Option.some.inj hr₂).symm
            rw [List.map_map] at hz₁ hz₂
            have := hrows _ _ _ hT₁ hT₂ xs
            simp only [P, Q] at this
            rw [show (fun c u => decide (Mean.d (B := S.sig) u < k) && (c.f o u).isSome) ∘ mng τ dL = P from rfl,
              show (fun c u => decide (Mean.d (B := S.sig) u < k) && (c.f o u).isSome) ∘ mng τ dR = Q from rfl] at *
            rw [hz₁, hz₂] at this
            exact nomatch this
      · rfl

/-! ### The object row -/

omit [Leaf S.sig] [Shapes S] in
/-- **Two objects apart at one name**: one side requires the name, and the two entries at the
    name share no datum of a smaller depth. -/
theorem obj_apart_at (F : MapA (Mean.V (B := S.sig)) (Mean.Mem (B := S.sig)) Mean.mem Mean.d)
    {s₁ s₂ : MapOf (FieldSem (Mean.V (B := S.sig)) (Mean.Mem (B := S.sig)))}
    {r₁ r₂ : RestSem (Mean.V (B := S.sig)) (Mean.Mem (B := S.sig))} {n : String} {k : Nat}
    (hreq : absentOf o (s₁.at n) = none ∨ absentOf o (s₂.at n) = none)
    (hE : ∀ u, Mean.d (B := S.sig) u < k →
      (((entryCodec s₁ (rcOf r₁) n).bind fun c => c.f o u).isSome &&
        ((entryCodec s₂ (rcOf r₂) n).bind fun c => c.f o u).isSome) = false) :
    ∀ v, Mean.d (B := S.sig) v < k + 1 →
      (((objectCodec F.toSummand s₁ r₁).f o v).isSome &&
        ((objectCodec F.toSummand s₂ r₂).f o v).isSome) = false := by
  intro v hv
  cases h1 : ((objectCodec F.toSummand s₁ r₁).f o v).isSome
  · rfl
  cases h2 : ((objectCodec F.toSummand s₂ r₂).f o v).isSome
  · rfl
  rw [objectCodec_f] at h1 h2
  cases hx : F.p.out v with
  | none => rw [hx] at h1; exact nomatch h1
  | some m =>
    rw [hx] at h1 h2
    simp only [Option.bind_some, Option.isSome_map] at h1 h2
    obtain ⟨hA1, hE1⟩ := objAt_isSome.mp h1
    obtain ⟨hA2, hE2⟩ := objAt_isSome.mp h2
    have hn : n ∈ m.keys := by
      rcases Decidable.em (n ∈ m.keys) with hn | hn
      · exact hn
      · exfalso
        rcases hreq with hr | hr
        · rcases Decidable.em (n ∈ s₁.keys) with hs | hs
          · have := hA1 n hs hn; rw [hr] at this; exact nomatch this
          · rw [MapOf.at_none hs] at hr; exact nomatch hr
        · rcases Decidable.em (n ∈ s₂.keys) with hs | hs
          · have := hA2 n hs hn; rw [hr] at this; exact nomatch this
          · rw [MapOf.at_none hs] at hr; exact nomatch hr
    have hd := F.d_lt m ⟨n, hn⟩
    rw [← F.p.into_out hx] at hd
    have := hE (m.get ⟨n, hn⟩) (by omega)
    rw [hE1 ⟨n, hn⟩, hE2 ⟨n, hn⟩] at this
    exact nomatch this

omit [Leaf S.sig] [Shapes S] in
/-- The codec of a field from a slot mode is the codec of the slot. -/
theorem fieldCodec_mkField (md : SlotMode S.sig) (c : Mean.C S.sig) : (mkField md c).codec = c := by
  cases md <;> rfl

omit [Leaf S.sig] [Shapes S] in
/-- **The entry of an object node at a name is the term of its slot.** -/
theorem entry_slot {N : Nat} (d : GSys τ N) {fs : Finset String}
    {md : {x // x ∈ fs} → SlotMode S.sig} {w : Fin 2} (a : (TOp.obj fs md w).Pos → Graph S.sig N)
    (n : String) (u : Mean.V (B := S.sig)) :
    ((entryCodec ⟨fs, fun x => mkField (md x) (mng τ d (a (.inl x)))⟩
        (rcOf (restOf w fun p => mng τ d (a (.inr p)))) n).bind fun c => c.f o u).isSome =
      ((mng τ d (slotAtG (md := md) a n).2).f o u).isSome := by
  unfold entryCodec slotAtG
  rcases Decidable.em (n ∈ fs) with h | h
  · rw [MapOf.at_of_mem (m := ⟨fs, _⟩) ⟨n, h⟩, dif_pos h]
    simp only [Option.bind_some, fieldCodec_mkField]
  · rw [MapOf.at_none (m := ⟨fs, _⟩) h, dif_neg h]
    match w with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl

omit [Leaf S.sig] [Shapes S] in
/-- A slot that requires the name refuses the absence of the name. -/
theorem absent_of_req {N : Nat} {fs : Finset String} {md : {x // x ∈ fs} → SlotMode S.sig}
    {w : Fin 2} (a : (TOp.obj fs md w).Pos → Graph S.sig N) (c : {x // x ∈ fs} → Mean.C S.sig)
    {n : String} (h : (slotAtG (md := md) a n).1.isReq = true) :
    absentOf o ((⟨fs, fun x => mkField (md x) (c x)⟩ : MapOf _).at n) = none := by
  unfold slotAtG at h
  rcases Decidable.em (n ∈ fs) with hn | hn
  · rw [dif_pos hn] at h
    rw [MapOf.at_of_mem (m := ⟨fs, _⟩) ⟨n, hn⟩]
    simp only
    cases hm : md ⟨n, hn⟩ with
    | req => rfl
    | opt => rw [hm] at h; exact nomatch h
    | fill _ => rw [hm] at h; exact nomatch h
  · rw [dif_neg hn] at h; exact nomatch h

omit [Sem S] [Leaf S.sig] [Shapes S] in
/-- A declared name holds its declared slot. -/
theorem slotAtG_mem {N : Nat} {fs : Finset String} {md : {x // x ∈ fs} → SlotMode S.sig}
    {w : Fin 2} (a : (TOp.obj fs md w).Pos → Graph S.sig N) (x : {x // x ∈ fs}) :
    slotAtG (md := md) a x.1 = (md x, a (.inl x)) := by
  unfold slotAtG; rw [dif_pos x.2]

omit [Leaf S.sig] in
/-- **The object row is sound.** -/
theorem objRow_sound {prev : Tbl NL NR → Graph S.sig NL → Graph S.sig NR → Bool}
    (hp : Prev τ (AB.rel o) dL dR prev) {fs : Finset String} {md : {x // x ∈ fs} → SlotMode S.sig}
    {w : Fin 2} (a : (TOp.obj fs md w).Pos → Graph S.sig NL) {A : Tbl NL NR} {k : Nat}
    (hA : Hyp τ (AB.rel o) dL dR k A) (y : Graph S.sig NR)
    (h : famObjG (md := md) (fun k => pairAt (sL := dL.sys) (sR := dR.sys) prev A (a (.inl k)))
        (blockTest (sL := dL.sys) (sR := dR.sys) (md := md) prev A w a) y = true) :
    AB o (k + 1) (mng τ dL (.node (.obj fs md w) a)) (mng τ dR y) := by
  cases y with
  | leaf _ => exact nomatch h
  | node op b =>
    cases op with
    | prim _ => exact AB.of_cls_node (op := .obj fs md w) (c := .object) (c' := .prim) (op' := .prim _) dR (fun p => mng τ dL (a p)) b rfl rfl (by decide)
    | set => exact AB.of_cls_node (op := .obj fs md w) (c := .object) (c' := .set) (op' := .set) dR (fun p => mng τ dL (a p)) b rfl rfl (by decide)
    | list _ _ _ => exact AB.of_cls_node (op := .obj fs md w) (c := .object) (c' := .list) (op' := .list _ _ _) dR (fun p => mng τ dL (a p)) b rfl rfl (by decide)
    | opaq => exact nomatch h
    | never => exact nomatch h
    | refine _ _ => exact nomatch h
    | held _ _ _ => exact nomatch h
    | legacy _ => exact nomatch h
    | union _ => exact nomatch h
    | obj fs' md' w' =>
      simp only [famObjG, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at h
      intro v hv
      show (((TOp.run τ (.obj fs md w) fun p => mng τ dL (a p)).f o v).isSome &&
        ((TOp.run τ (.obj fs' md' w') fun p => mng τ dR (b p)).f o v).isSome) = false
      simp only [TOp.run]
      split
      · next F hF =>
        rcases h with ⟨x, _, hr, hg⟩ | ⟨x, _, ⟨hx, hr⟩, hmw⟩
        · have hab := pairAt_soundR hp _ _ A k hg hA
          refine obj_apart_at F (n := x.1) ?_ (fun u hu => ?_) v hv
          · rcases hr with hr | hr
            · refine Or.inl (absent_of_req a _ ?_)
              rw [slotAtG_mem a x]; exact hr
            · exact Or.inr (absent_of_req b _ hr)
          · rw [entry_slot dL a, entry_slot dR b, slotAtG_mem a x]
            exact hab u hu
        · have hxn : x.1 ∉ fs := by simpa using hx
          refine obj_apart_at F (n := x.1) (Or.inr (absent_of_req b _ ?_)) (fun u hu => ?_) v hv
          · rw [slotAtG_mem b x]; exact hr
          · rw [entry_slot dL a, entry_slot dR b, slotAtG_mem b x]
            unfold slotAtG
            rw [dif_neg hxn]
            match w, a, hmw with
            | ⟨0, _⟩, _, _ => simp only [Graph.never]; rfl
            | ⟨1, _⟩, a, hmw =>
              exact pairAt_soundR hp _ _ A k hmw hA u hu
      · rfl

/-! ### A graph term below the top -/

omit [Leaf S.sig] [Shapes S] in
/-- A member of a count of zero or one is a value of the function. -/
theorem optOf_mem {X : Type} : ∀ (s : Fin 2) (f : Fin s → X) (c : X), c ∈ optOf s f → ∃ p, f p = c
  | ⟨0, _⟩, _, _, h => nomatch h
  | ⟨1, _⟩, _, _, h => by cases h; exact ⟨_, rfl⟩

omit [Leaf S.sig] [Shapes S] in
/-- The codec of an open block is a value of the function of the block. -/
theorem restOf_mem : ∀ (s : Fin 2) (f : Fin s → Mean.C S.sig) (c : Mean.C S.sig),
    c ∈ rcOf (restOf s f) → ∃ p, f p = c
  | ⟨0, _⟩, _, _, h => nomatch h
  | ⟨1, _⟩, _, _, h => by cases h; exact ⟨_, rfl⟩

omit [Leaf S.sig] [Shapes S] in
/-- **An operation with no adapter keeps the top**: over arguments below the top, it is below the
    top. -/
theorem sub_run [TopLaws S] {op : TOp S.sig} (hop : op.adapts = false) {a : op.Pos → Mean.C S.sig}
    (h : ∀ p, Sub (a p) (Syn.top (S := S))) : Sub (TOp.run τ op a) (Syn.top (S := S)) := by
  cases op with
  | prim g => exact TopLaws.ground g
  | opaq => exact fun _ _ _ h => h
  | never => exact sub_empty
  | set =>
    simp only [TOp.run]
    split
    · next L hL => exact TopLaws.set L hL _ (h ())
    · exact sub_empty
  | list n s m =>
    simp only [TOp.run]
    split
    · next L hL =>
      refine sub_listCodec (fun _ => top_list L.p.into) (fun c hc => ?_) (fun c hc => ?_)
        (fun c hc => ?_)
      · obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hc; exact h _
      · obtain ⟨p, rfl⟩ := optOf_mem _ _ _ hc; exact h _
      · obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hc; exact h _
    · exact sub_empty
  | refine q qA => exact sub_trans (sub_refine2_self _ _ _) (h ())
  | held _ _ _ => exact nomatch hop
  | legacy _ => exact nomatch hop
  | obj fs md w =>
    simp only [TOp.run]
    split
    · next F hF =>
      have hnf : noFill (⟨fs, fun x => mkField (md x) (a (.inl x))⟩ : MapOf _) = true :=
        decide_eq_true fun x => by
          simp only [TOp.adapts, List.any_eq_false] at hop
          have hx := hop x (keyPos_complete fs x)
          show (mkField (md x) (a (.inl x))).isFill = false
          cases hm : md x with
          | req => rfl
          | opt => rfl
          | fill _ => rw [hm] at hx; exact absurd rfl hx
      refine sub_objectCodec (fun _ => top_map F.p.into) hnf (fun x => ?_) (fun c hc => ?_)
      · rw [fieldCodec_mkField]; exact h _
      · obtain ⟨p, rfl⟩ := restOf_mem _ _ _ hc; exact h _
    · exact sub_empty
  | union m =>
    exact sub_altCodec (fun c hc => by obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hc; exact h p) _

/-- Below the top at each datum of depth at most `d`. -/
def SubLe (d : Nat) (c : Mean.C S.sig) : Prop :=
  ∀ o x y, Mean.d (B := S.sig) x ≤ d → c.f o x = some y → (Syn.top (S := S)).f o x = some y

/-- A codec cut at a depth. -/
def trunc (d : Nat) (c : Mean.C S.sig) : Mean.C S.sig where
  T := c.T
  μ := c.μ
  f o x := if Mean.d (B := S.sig) x ≤ d then c.f o x else none

omit [Leaf S.sig] [Shapes S] in
/-- A codec cut at a depth agrees with the codec at that depth. -/
theorem trunc_agree (d : Nat) (c : Mean.C S.sig) : AgreeLe Mean.d d (trunc d c) c :=
  ⟨fun o x hx => by simp only [trunc, if_pos hx]⟩

omit [Leaf S.sig] [Shapes S] in
/-- A codec below the top at a depth gives a cut codec below the top. -/
theorem sub_trunc {d : Nat} {c : Mean.C S.sig} (h : SubLe d c) : Sub (trunc d c) (Syn.top (S := S)) :=
  fun o x y hxy => by
    simp only [trunc] at hxy
    split at hxy
    · next hx => exact h o x y hx hxy
    · exact nomatch hxy

omit [Leaf S.sig] [Shapes S] in
/-- A codec that agrees with a codec below the top is below the top at the depth of the agreement. -/
theorem SubLe.of_agree {d : Nat} {c c' : Mean.C S.sig} (hs : Sub c (Syn.top (S := S)))
    (ha : AgreeLe Mean.d d c c') : SubLe d c' := fun o x y hx h => by
  rw [← ha.f o x hx] at h; exact hs o x y h

omit [Leaf S.sig] [Shapes S] in
/-- A codec below the top at a depth is below the top at each smaller depth. -/
theorem SubLe.mono {d d' : Nat} {c : Mean.C S.sig} (hd : d' ≤ d) (h : SubLe d c) : SubLe d' c :=
  fun o x y hx hxy => h o x y (by omega) hxy

omit [Leaf S.sig] [Shapes S] in
/-- Each codec is below the top at the depth zero. -/
theorem SubLe.zero (c : Mean.C S.sig) : SubLe 0 c :=
  fun _ x _ hx _ => absurd hx (Nat.not_le.mpr (Mean.d_pos x))

omit [Leaf S.sig] [Shapes S] in
/-- A `keep` operation with no adapter keeps the depth of its arguments below the top. -/
theorem SubLe.keep [TopLaws S] {op : TOp S.sig} (hop : op.adapts = false) (hk : op.kind = .keep)
    {d : Nat} {a : op.Pos → Mean.C S.sig} (h : ∀ p, SubLe d (a p)) : SubLe d (TOp.run τ op a) :=
  SubLe.of_agree (sub_run hop fun p => sub_trunc (h p))
    ((TStep_lawful τ).keep op hk d _ _ fun p => trunc_agree d (a p))

omit [Leaf S.sig] [Shapes S] in
/-- A `down` operation with no adapter adds one depth below the top. -/
theorem SubLe.down [TopLaws S] {op : TOp S.sig} (hop : op.adapts = false) (hk : op.kind = .down)
    {d : Nat} {a : op.Pos → Mean.C S.sig} (h : ∀ p, SubLe d (a p)) : SubLe (d + 1) (TOp.run τ op a) :=
  SubLe.of_agree (sub_run hop fun p => sub_trunc (h p))
    ((TStep_lawful τ).down op hk d _ _ fun p => trunc_agree d (a p))

omit [Sem S] [Leaf S.sig] [Shapes S] in
/-- Each operation is a `keep`, a `down`, or a wall. -/
theorem TOp.kind_cases (op : TOp S.sig) : op.kind = .keep ∨ op.kind = .down ∨ op.kind = .wall := by
  cases op <;> simp [TOp.kind]

omit [Sem S] [Leaf S.sig] [Shapes S] in
/-- Each wall is an adapter. -/
theorem TOp.adapts_of_wall {op : TOp S.sig} (h : op.kind = .wall) : op.adapts = true := by
  cases op <;> first | rfl | exact nomatch h

omit [Sem S] [Leaf S.sig] [Shapes S] in
/-- An entry at an unguarded leaf of a term with no adapter has no adapter. -/
theorem adapts_ulv {N : Nat} {ad : Fin N → Bool} {j : Fin N} :
    ∀ t : Graph S.sig N, Graph.adapts ad t = false → t.ulv (TSig S.sig) j = true → ad j = false
  | .leaf i, ht, hj => by
    have : i = j := of_decide_eq_true hj
    subst this; exact ht
  | .node op a, ht, hj => by
    simp only [Graph.adapts, Bool.or_eq_false_iff, List.any_eq_false] at ht
    simp only [Flat.ulv] at hj
    split at hj
    · obtain ⟨p, -, hp⟩ := List.any_eq_true.mp hj
      exact adapts_ulv (a p) (Bool.eq_false_iff.mpr (ht.2 p (op.pos_complete p))) hp
    · exact nomatch hj

omit [Leaf S.sig] [Shapes S] in
/-- **A term with no adapter is below the top at a depth**, where each entry with no adapter is. -/
theorem SubLe.term [TopLaws S] {N : Nat} (dd : GSys τ N) {ad : Fin N → Bool} :
    ∀ (t : Graph S.sig N) (d : Nat), Graph.adapts ad t = false →
      (∀ j, ad j = false → SubLe d (mng τ dd (.leaf j))) → SubLe d (mng τ dd t)
  | .leaf j, _, ht, h => h j ht
  | .node op a, d, ht, h => by
    simp only [Graph.adapts, Bool.or_eq_false_iff, List.any_eq_false] at ht
    have hc : ∀ p, Graph.adapts ad (a p) = false := fun p => Bool.eq_false_iff.mpr (ht.2 p (op.pos_complete p))
    rcases TOp.kind_cases op with hk | hk | hk
    · exact SubLe.keep ht.1 hk fun p => SubLe.term dd (a p) d (hc p) h
    · cases d with
      | zero => exact SubLe.zero _
      | succ d =>
        exact SubLe.down ht.1 hk fun p =>
          SubLe.term dd (a p) d (hc p) fun j hj => (h j hj).mono (Nat.le_succ d)
    · rw [TOp.adapts_of_wall hk] at ht; exact nomatch ht.1

omit [Leaf S.sig] [Shapes S] in
/-- …and one depth deeper, where each entry at an unguarded leaf is one depth deeper. -/
theorem SubLe.termU [TopLaws S] {N : Nat} (dd : GSys τ N) {ad : Fin N → Bool} {d : Nat}
    (hall : ∀ j, ad j = false → SubLe d (mng τ dd (.leaf j))) :
    ∀ t : Graph S.sig N, t.adapts ad = false →
      (∀ j, t.ulv (TSig S.sig) j = true → SubLe (d + 1) (mng τ dd (.leaf j))) →
        SubLe (d + 1) (mng τ dd t)
  | .leaf j, _, h => h j (decide_eq_true rfl)
  | .node op a, ht, h => by
    simp only [Graph.adapts, Bool.or_eq_false_iff, List.any_eq_false] at ht
    have hc : ∀ p, Graph.adapts ad (a p) = false := fun p => Bool.eq_false_iff.mpr (ht.2 p (op.pos_complete p))
    rcases TOp.kind_cases op with hk | hk | hk
    · refine SubLe.keep ht.1 hk fun p => SubLe.termU dd hall (a p) (hc p) fun j hj => h j ?_
      simp only [Flat.ulv, show (TSig S.sig).kind op = .keep from hk]
      exact List.any_eq_true.mpr ⟨p, (TSig S.sig).pos_complete op p, hj⟩
    · exact SubLe.down ht.1 hk fun p => SubLe.term dd (a p) d (hc p) hall
    · rw [TOp.adapts_of_wall hk] at ht; exact nomatch ht.1

omit [Leaf S.sig] [Shapes S] in
/-- **The entries with no adapter are below the top**, by induction on the depth, and at one depth
    by induction on the longest walk of unguarded edges, which the absence of a cycle bounds. -/
theorem sub_entries [TopLaws S] {N : Nat} (dd : GSys τ N) (hst : adStable dd.sys = true) :
    ∀ d j, adOf dd.sys j = false → SubLe d (mng τ dd (.leaf j)) := by
  have hstab : ∀ i, adOf dd.sys i = false → Graph.adapts (adOf dd.sys) (dd.sys i) = false := by
    intro i hi
    simp only [adStable, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hst
    rw [hst i, hi]
  intro d
  induction d with
  | zero => exact fun _ _ => SubLe.zero _
  | succ d ih =>
    have hQ : ∀ m i, ¬ WalkFrom (TSig S.sig) dd.sys m i → adOf dd.sys i = false →
        SubLe (d + 1) (mng τ dd (.leaf i)) := by
      intro m
      induction m with
      | zero => exact fun i hw _ => absurd ⟨fun _ => i, rfl, fun _ ht => absurd ht (Nat.not_lt_zero _)⟩ hw
      | succ m ihm =>
        intro i hw hi
        have hT := SubLe.termU dd ih (dd.sys i) (hstab i hi) fun j hj => by
          have hjw : ¬ WalkFrom (TSig S.sig) dd.sys m j := fun hwj => hw (walk_cons hj hwj)
          have hjad : adOf dd.sys j = false := adapts_ulv _ (hstab i hi) hj
          exact ihm j hjw hjad
        intro o x y hx hxy
        rw [mng_leaf dd i] at hxy
        exact hT o x y hx hxy
    intro j hj
    exact hQ N j (fun hw => dd.noCycle (cycle_of_walk hw)) hj

omit [Leaf S.sig] [Shapes S] in
/-- **A graph term below the top denotes a restriction of the top.** -/
theorem sub_of_belowTop [TopLaws S] {N : Nat} (dd : GSys τ N) {t : Graph S.sig N}
    (h : belowTop dd.sys t = true) : Sub (mng τ dd t) (Syn.top (S := S)) := by
  simp only [belowTop, Bool.and_eq_true, Bool.not_eq_true'] at h
  intro o x y hxy
  exact SubLe.term dd t _ h.2 (fun j hj => sub_entries dd h.1 _ j hj) o x y (Nat.le_refl _) hxy

/-- **The rows are sound**, by induction on the left operand. -/
theorem rowG_sound (laws : Laws S o) {prev : Tbl NL NR → Graph S.sig NL → Graph S.sig NR → Bool}
    (hp : Prev τ (AB.rel o) dL dR prev) :
    ∀ x y A k, rowG dL.sys dR.sys prev A x y = true → Hyp τ (AB.rel o) dL dR k A →
      AB o (k + 1) (mng τ dL x) (mng τ dR y) := by
  intro x
  induction x with
  | leaf j =>
    intro y A k h hA
    rw [rowG] at h
    exact AB.congr (mng_leaf dL j).symm rfl (hp A _ y h k hA)
  | node op a ih =>
    intro y A k h hA
    have hr : ∀ y', prev A (.node op a) y' = true → AB o (k + 1) (mng τ dL (.node op a)) (mng τ dR y') :=
      fun y' h' => hp A _ y' h' k hA
    cases op with
    | never =>
      rw [rowG] at h
      exact AB.of_left fun _ => rfl
    | held _ _ _ =>
      rw [rowG] at h
      exact AB.of_rightC dR (fam := fun _ => false) hr (fun _ h' => absurd h' Bool.false_ne_true) y h
    | legacy _ =>
      rw [rowG] at h
      exact AB.of_rightC dR (fam := fun _ => false) hr (fun _ h' => absurd h' Bool.false_ne_true) y h
    | opaq =>
      rw [rowG] at h
      exact AB.of_rightC dR (fam := fun _ => false) hr (fun _ h' => absurd h' Bool.false_ne_true) y h
    | union m =>
      simp only [rowG, List.all_eq_true, List.mem_finRange, true_implies] at h
      exact AB.union_left fun p => ih p y A k (h p) hA
    | prim g =>
      rw [rowG] at h
      exact AB.of_rightC dR hr (famPrimG_sound laws dR (fun p => mng τ dL (a p))) y h
    | set =>
      rw [rowG] at h
      exact AB.of_rightC dR hr (famSetG_sound laws dR (fun p => mng τ dL (a p)) fun e he =>
        apart_of_AB fun k' => hp [] (a ()) e he k' fun _ hq => nomatch hq) y h
    | list _ _ _ =>
      rw [rowG] at h
      exact AB.of_rightC dR hr (fun y' h' => listRow_sound hp a hA y' h') y h
    | obj _ _ _ =>
      rw [rowG] at h
      exact AB.of_rightC dR hr (fun y' h' => objRow_sound hp a hA y' h') y h
    | refine q qA =>
      rw [rowG] at h
      exact AB.refine_left (ih () y A k h hA)

/-- **The walk is sound at every fuel.** -/
theorem decG_sound (laws : Laws S o) : ∀ n, Prev τ (AB.rel o) dL dR (decG dL.sys dR.sys n)
  | 0 => fun _ _ _ h => nomatch h
  | n + 1 => fun A x y h k hA => rowG_sound laws (decG_sound laws n) x y A k h hA

end Sound

/-- **Soundness of the decision**: where `disjoint` answers `true`, no datum is accepted by both
    meanings at the orientation. -/
theorem disjoint_sound {S : Syn} [Sem S] [Leaf S.sig] [Shapes S]
    {τ : (s : Bool) → TableAt S.sig s} {o : Orient} (laws : Laws S o) {NL NR : Nat}
    {dL : Closed S.sig NL} {dR : Closed S.sig NR} {rL : Fin NL} {rR : Fin NR}
    (h : disjoint dL rL dR rR = true) (v : Mean.V (B := S.sig)) :
    (((Closed.meaning τ dL rL).f o v).isSome && ((Closed.meaning τ dR rR).f o v).isSome) = false :=
  apart_of_AB (fun k => decG_sound (dL := Closed.toG τ dL) (dR := Closed.toG τ dR) laws _ []
    (.leaf rL) (.leaf rR) h k fun _ hq => nomatch hq) v


/-! ## The view of a closed codec -/

section ViewSound
variable {B : Sig} [Mean B] {N : Nat} (sys : Fin N → Graph B N) (o : Orient)

omit [Mean B] in
/-- A node that is not a wall, over arguments with no leaf below a wall, has no leaf below a wall. -/
theorem okB_node_nonwall {op : TOp B} (hk : op.kind ≠ .wall) {g : op.Pos → Graph B N}
    (h : ∀ p, (g p).okB (TSig B) = true) : (Flat.node op g).okB (TSig B) = true :=
  Flat.okB_node_iff.mpr ⟨fun h' => absurd h' hk, fun _ p => h p⟩

/-- **The view holds no wall.** -/
theorem okB_viewG : ∀ t : Graph B N, (viewG sys o t).okB (TSig B) = true := by
  intro t
  induction t with
  | leaf _ => rfl
  | node op a ih =>
    cases op with
    | held s _ _ =>
      simp only [viewG]
      cases (s == o.c) <;> simp only [cond_true, cond_false] <;> exact ih _
    | legacy _ =>
      simp only [viewG]
      cases o.c <;> simp only [cond_true, cond_false]
      · exact ih ()
      · exact okB_node_nonwall (op := .opaq) (fun h => nomatch h) fun p => nomatch p
    | refine p pA =>
      simp only [viewG]
      split
      · exact okB_node_nonwall (op := .refine _ _) (fun h => nomatch h) fun _ => ih ()
      · exact okB_node_nonwall (op := .refine _ _) (fun h => nomatch h) fun _ => ih ()
    | obj fs md w => exact okB_node_nonwall (op := .obj _ _ _) (fun h => nomatch h) fun p => ih p
    | prim _ => exact okB_node_nonwall (op := .prim _) (fun h => nomatch h) fun p => ih p
    | opaq => exact okB_node_nonwall (op := .opaq) (fun h => nomatch h) fun p => ih p
    | never => exact okB_node_nonwall (op := .never) (fun h => nomatch h) fun p => ih p
    | set => exact okB_node_nonwall (op := .set) (fun h => nomatch h) fun p => ih p
    | list _ _ _ => exact okB_node_nonwall (op := .list _ _ _) (fun h => nomatch h) fun p => ih p
    | union _ => exact okB_node_nonwall (op := .union _) (fun h => nomatch h) fun p => ih p

/-- **The view keeps each leaf of the term.** -/
theorem lv_viewG {j : Fin N} : ∀ t : Graph B N, (viewG sys o t).lv (TSig B) j = true →
    t.lv (TSig B) j = true := by
  intro t
  induction t with
  | leaf _ => exact id
  | node op a ih =>
    intro h
    have hc : ∀ p, (a p).lv (TSig B) j = true → (Flat.node op a).lv (TSig B) j = true :=
      fun p hp => Flat.lv_node.mpr ⟨p, hp⟩
    have hn : ∀ {op' : TOp B} {g : op'.Pos → Graph B N}, (∀ p, (g p).lv (TSig B) j = true →
        ∃ q, (a q).lv (TSig B) j = true) → (Flat.node op' g).lv (TSig B) j = true →
          (Flat.node op a).lv (TSig B) j = true := fun hg h' => by
      obtain ⟨p, hp⟩ := Flat.lv_node.mp h'
      obtain ⟨q, hq⟩ := hg p hp
      exact hc q hq
    cases op with
    | held s _ _ =>
      simp only [viewG] at h
      cases hs : (s == o.c) <;> rw [hs] at h <;> simp only [cond_true, cond_false] at h
      · exact hc _ (ih _ h)
      · exact hc _ (ih _ h)
    | legacy _ =>
      simp only [viewG] at h
      cases hs : o.c <;> rw [hs] at h <;> simp only [cond_true, cond_false] at h
      · exact hc _ (ih _ h)
      · obtain ⟨p, -⟩ := Flat.lv_node.mp h; exact nomatch p
    | refine p pA =>
      simp only [viewG] at h
      split at h
      · exact hn (op' := .refine p pA) (fun _ hp => ⟨(), ih () hp⟩) h
      · exact hn (op' := .refine _ _) (fun _ hp => ⟨(), ih () hp⟩) h
    | obj fs md w => exact hn (op' := .obj fs (fun x => SlotMode.view o (md x)) w) (fun p hp => ⟨p, ih p hp⟩) h
    | prim g => exact hn (op' := .prim g) (fun p hp => ⟨p, ih p hp⟩) h
    | opaq => exact hn (op' := .opaq) (fun p hp => ⟨p, ih p hp⟩) h
    | never => exact hn (op' := .never) (fun p hp => ⟨p, ih p hp⟩) h
    | set => exact hn (op' := .set) (fun p hp => ⟨p, ih p hp⟩) h
    | list n s m => exact hn (op' := .list n s m) (fun p hp => ⟨p, ih p hp⟩) h
    | union m => exact hn (op' := .union m) (fun p hp => ⟨p, ih p hp⟩) h

/-- **An unguarded leaf of the view is an unguarded leaf of the term, or a leaf below a wall.** -/
theorem ulv_viewG {j : Fin N} : ∀ t : Graph B N, (viewG sys o t).ulv (TSig B) j = true →
    t.ulv (TSig B) j = true ∨ t.wlv (TSig B) j = true := by
  intro t
  induction t with
  | leaf _ => exact Or.inl
  | node op a ih =>
    intro h
    -- a keep node of the view over the views of the arguments
    have keepCase : ∀ {op' : TOp B} {g : op'.Pos → Graph B N}, op.kind = .keep →
        (∀ p, (g p).ulv (TSig B) j = true → ∃ q, (a q).ulv (TSig B) j = true ∨ (a q).wlv (TSig B) j = true) →
        (Flat.node op' g).ulv (TSig B) j = true →
          (Flat.node op a).ulv (TSig B) j = true ∨ (Flat.node op a).wlv (TSig B) j = true := by
      intro op' g hk hg h'
      obtain ⟨-, p, hp⟩ := Flat.ulv_node_iff.mp h'
      obtain ⟨q, hq | hq⟩ := hg p hp
      · exact Or.inl (Flat.ulv_node_iff.mpr ⟨hk, q, hq⟩)
      · exact Or.inr (Flat.wlv_node.mpr (Or.inr ⟨(fun h'' => absurd (hk.symm.trans h'') (fun h => nomatch h)), q, hq⟩))
    have wallCase : op.kind = .wall → ∀ p, (viewG sys o (a p)).ulv (TSig B) j = true →
        (Flat.node op a).wlv (TSig B) j = true := fun hk p hp =>
      Flat.wlv_node.mpr (Or.inl ⟨hk, p, lv_viewG sys o _ (Flat.lv_of_ulv _ hp)⟩)
    cases op with
    | held s _ _ =>
      simp only [viewG] at h
      cases hs : (s == o.c) <;> rw [hs] at h <;> simp only [cond_true, cond_false] at h
      · exact Or.inr (wallCase rfl _ h)
      · exact Or.inr (wallCase rfl _ h)
    | legacy _ =>
      simp only [viewG] at h
      cases hs : o.c <;> rw [hs] at h <;> simp only [cond_true, cond_false] at h
      · exact Or.inr (wallCase rfl _ h)
      · obtain ⟨-, p, -⟩ := Flat.ulv_node_iff.mp h; exact nomatch p
    | refine p pA =>
      simp only [viewG] at h
      split at h
      · exact keepCase (op' := .refine p pA) rfl (fun _ hp => ⟨(), ih () hp⟩) h
      · exact keepCase (op' := .refine _ _) rfl (fun _ hp => ⟨(), ih () hp⟩) h
    | union m => exact keepCase (op' := .union m) rfl (fun p hp => ⟨p, ih p hp⟩) h
    | prim g => exact keepCase (op' := .prim g) rfl (fun p hp => ⟨p, ih p hp⟩) h
    | opaq => exact keepCase (op' := .opaq) rfl (fun p hp => ⟨p, ih p hp⟩) h
    | never => exact keepCase (op' := .never) rfl (fun p hp => ⟨p, ih p hp⟩) h
    | set => obtain ⟨hk, -⟩ := Flat.ulv_node_iff.mp h; exact nomatch hk
    | list _ _ _ => obtain ⟨hk, -⟩ := Flat.ulv_node_iff.mp h; exact nomatch hk
    | obj _ _ _ => obtain ⟨hk, -⟩ := Flat.ulv_node_iff.mp h; exact nomatch hk

/-- **The view holds no adapter.** -/
theorem adapts_viewG : ∀ t : Graph B N, Graph.adapts (fun _ => false) (viewG sys o t) = false := by
  intro t
  induction t with
  | leaf _ => rfl
  | node op a ih =>
    have hn : ∀ {op' : TOp B} {g : op'.Pos → Graph B N}, op'.adapts = false →
        (∀ p, Graph.adapts (fun _ => false) (g p) = false) →
          Graph.adapts (fun _ => false) (Flat.node op' g) = false := fun ho hg => by
      simp only [Graph.adapts, ho, Bool.false_or, List.any_eq_false]
      exact fun p _ => by rw [hg p]; exact Bool.false_ne_true
    cases op with
    | held s _ _ =>
      simp only [viewG]
      cases (s == o.c) <;> simp only [cond_true, cond_false] <;> exact ih _
    | legacy _ =>
      simp only [viewG]
      cases o.c <;> simp only [cond_true, cond_false]
      · exact ih ()
      · exact hn (op' := .opaq) rfl fun p => nomatch p
    | refine p pA =>
      simp only [viewG]
      split
      · exact hn (op' := .refine _ _) rfl fun _ => ih ()
      · exact hn (op' := .refine _ _) rfl fun _ => ih ()
    | obj fs md w =>
      refine hn (op' := .obj fs (fun x => SlotMode.view o (md x)) w) ?_ fun p => ih p
      simp only [TOp.adapts, List.any_eq_false]
      intro x _
      cases hm : md x with
      | req => simp only [SlotMode.view]; exact Bool.false_ne_true
      | opt => simp only [SlotMode.view]; exact Bool.false_ne_true
      | fill _ => simp only [hm, SlotMode.view]; cases o.c <;> simp
    | prim g => exact hn (op' := .prim g) rfl fun p => ih p
    | opaq => exact hn (op' := .opaq) rfl fun p => ih p
    | never => exact hn (op' := .never) rfl fun p => ih p
    | set => exact hn (op' := .set) rfl fun p => ih p
    | list n s m => exact hn (op' := .list n s m) rfl fun p => ih p
    | union m => exact hn (op' := .union m) rfl fun p => ih p

/-- The view system has no adapter at any entry. -/
theorem adIter_viewSys : ∀ n, adIter (viewSys sys o) n = fun _ => false
  | 0 => rfl
  | n + 1 => funext fun i => by
      show Graph.adapts (adIter (viewSys sys o) n) (viewG sys o (sys i)) = false
      rw [adIter_viewSys n]; exact adapts_viewG sys o _

/-- The table of adapters of a view system is a fixed point. -/
theorem adStable_viewSys : adStable (viewSys sys o) = true := by
  simp only [adStable, adOf, adIter_viewSys, List.all_eq_true]
  intro i _
  rw [show Graph.adapts (fun _ => false) (viewSys sys o i) = false from adapts_viewG sys o _]
  rfl

/-- **Each view term lies below the top.** -/
theorem belowTop_viewG (t : Graph B N) : belowTop (viewSys sys o) (viewG sys o t) = true := by
  simp only [belowTop, adStable_viewSys, adOf, adIter_viewSys, Bool.true_and]
  rw [adapts_viewG]; rfl

end ViewSound

/-! ## The view admits what the term admits -/

section ViewLe
variable {S : Syn} [Sem S] (τ : (s : Bool) → TableAt S.sig s) (o : Orient)

/-- **The unguarded edges of a view lower the entry**, so the view of a closed codec has no cycle
    of unguarded edges. -/
theorem viewSys_noCycle {N : Nat} (d : Closed S.sig N) : ¬ Cycle (TSig S.sig) (viewSys d.graph o) :=
  noCycle_of_rank (fun i => i.val) fun i j h => by
    rcases ulv_viewG d.graph o (d.graph i) h with h | h
    · exact (SSys.order d).1 i j h
    · exact absurd h (by rw [(SSys.order d).2 i j]; decide)

/-- **The graph system of the view of a closed codec**: its view, and the solution of the view. -/
def Closed.viewToG {N : Nat} (d : Closed S.sig N) : GSys τ N where
  sys := viewSys d.graph o
  e := solve Mean.d (sysB (TStep τ) (elim (TSig S.sig) (viewSys d.graph o) N))
  fix := (elim_solution Mean.d_pos (TStep_lawful τ)
    (fun i => Flat.ok_of_okB _ (okB_viewG d.graph o _))
    (elim_guarded (fun i => okB_viewG d.graph o _) (viewSys_noCycle o d))).1
  noCycle := viewSys_noCycle o d

variable {τ o}

/-- Acceptance below a depth, from one codec to another. -/
def LeK (k : Nat) (c c' : Mean.C S.sig) : Prop :=
  ∀ x, Mean.d (B := S.sig) x ≤ k → (c.f o x).isSome = true → (c'.f o x).isSome = true

/-- Acceptance from one codec to another below a depth holds below each smaller depth. -/
theorem LeK.mono {k k' : Nat} {c c' : Mean.C S.sig} (hk : k' ≤ k) (h : LeK (o := o) k c c') :
    LeK (o := o) k' c c' := fun x hx => h x (by omega)

/-- Acceptance from one codec to another holds below the depth zero. -/
theorem LeK.zero (c c' : Mean.C S.sig) : LeK (o := o) 0 c c' :=
  fun x hx _ => absurd hx (Nat.not_le.mpr (Mean.d_pos x))

/-- A union over options that accept more accepts more. -/
theorem LeK.union {k m : Nat} {a b : Fin m → Mean.C S.sig} {μ μ' : Option (Mean.Mem (B := S.sig))}
    (h : ∀ p, LeK (o := o) k (a p) (b p)) :
    LeK (o := o) k (altCodec (List.ofFn a) μ) (altCodec (List.ofFn b) μ') := fun x hx hA => by
  obtain ⟨p, hp⟩ := union_acc hA
  refine (select_isSome_attempt _ _ _).mpr ⟨b p, List.mem_ofFn.mpr ⟨p, rfl⟩, h p x hx hp⟩

/-- A traversal over positions that accept more succeeds where the first traversal succeeds. -/
theorem LeK.trav {k : Nat} : ∀ (row row' : List (Mean.C S.sig)) (xs : List (Mean.V (B := S.sig))),
    List.Forall₂ (LeK (o := o) k) row row' → (∀ x ∈ xs, Mean.d (B := S.sig) x ≤ k) →
      (traverse (fun cx : Mean.C S.sig × Mean.V (B := S.sig) => cx.1.f o cx.2) (row.zip xs)).isSome = true →
        (traverse (fun cx : Mean.C S.sig × Mean.V (B := S.sig) => cx.1.f o cx.2) (row'.zip xs)).isSome = true
  | [], [], _, .nil, _, h => h
  | _ :: _, _ :: _, [], .cons _ _, _, h => h
  | c :: cs, c' :: cs', x :: xs, .cons hc hcs, hd, h => by
      rw [List.zip_cons_cons, traverse_cons_isSome, Bool.and_eq_true] at h ⊢
      exact ⟨hc x (hd x List.mem_cons_self) h.1,
        LeK.trav cs cs' xs hcs (fun y hy => hd y (List.mem_cons_of_mem _ hy)) h.2⟩

/-- **A list over positions that accept more accepts more**, one depth down. -/
theorem LeK.list (L : ListA (Mean.V (B := S.sig)) (Mean.Mem (B := S.sig)) Mean.mem Mean.d) {k : Nat}
    {pre pre' suf suf' : List (Mean.C S.sig)} {sp sp' : Option (Mean.C S.sig)}
    (hp : List.Forall₂ (LeK (o := o) k) pre pre') (hs : Option.Rel (LeK (o := o) k) sp sp')
    (hf : List.Forall₂ (LeK (o := o) k) suf suf') :
    LeK (o := o) (k + 1) (listCodec L.toSummand pre sp suf) (listCodec L.toSummand pre' sp' suf') := by
  intro v hv h
  rw [listCodec_f] at h ⊢
  cases hx : L.p.out v with
  | none => rw [hx] at h; exact nomatch h
  | some xs =>
    rw [hx] at h
    simp only [Option.bind_some, Option.isSome_map] at h ⊢
    unfold alignL at h ⊢
    have hr := slotsL_rel hp hs hf xs.length
    cases h1 : slotsL pre sp suf xs.length with
    | none => rw [h1] at h; exact nomatch h
    | some row =>
      rw [h1] at h hr
      cases h2 : slotsL pre' sp' suf' xs.length with
      | none => rw [h2] at hr; exact nomatch hr
      | some row' =>
        rw [h2] at hr
        simp only [Option.map_some, Option.bind_some] at h ⊢
        have hvx := L.p.into_out hx
        refine LeK.trav row row' xs (by cases hr; assumption) (fun u hu => ?_) h
        have := L.d_lt xs u hu
        rw [← hvx] at this
        omega

omit [Sem S] in
/-- An orientation has the caller side `false` and the stored side `true`, or the reverse. -/
theorem orient_cases (o : Orient) : (o.c = false ∧ o.s = true) ∨ (o.c = true ∧ o.s = false) := by
  obtain ⟨⟨c, s⟩, h⟩ := o
  cases c <;> cases s
  · exact absurd rfl h
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact absurd rfl h

/-- **A set over an element that accepts more accepts more**, one depth down: the set reads its
    element below the depth of the set, and the set law of the top carries the inclusion. -/
theorem LeK.set [TopLaws S] (L : SetF (Mean.V (B := S.sig)) (Mean.Mem (B := S.sig)) Mean.mem Mean.d)
    (hL : Mean.set (B := S.sig) = some L) {k : Nat} {c c' : Mean.C S.sig} (h : LeK (o := o) k c c')
    (hsub : Sub c' (Syn.top (S := S))) : LeK (o := o) (k + 1) (L.lift c) (L.lift c') := by
  intro v hv hA
  have hag : AgreeLe Mean.d (k + 1) (L.lift (trunc k c)) (L.lift c) := L.agree (trunc_agree k c)
  have hA' : ((L.lift (trunc k c)).f o v).isSome = true := by rw [hag.f o v hv]; exact hA
  refine TopLaws.set_mono L hL o (trunc k c) c' hsub (fun w hw => ?_) v hA'
  simp only [trunc] at hw
  split at hw
  · next hd => exact h w hd hw
  · exact nomatch hw

/-- **A `held` admits at an orientation only what its term at the caller side admits.** -/
theorem held1_acc {s : Bool} {c P : Mean.C S.sig} {w : PairAt (Mean.V (B := S.sig))}
    {v : Mean.V (B := S.sig)} (h : ((held1 s c P w).f o v).isSome = true) :
    (s = o.c → (P.f o v).isSome = true) ∧ (s ≠ o.c → (c.f o v).isSome = true) := by
  obtain ⟨⟨c₀, s₀⟩, ho⟩ := o
  unfold held1 at h
  rw [refine2_f_isSome, Bool.and_eq_true] at h
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · subst hs
    rename_i s
    cases s <;> cases s₀
    · exact absurd rfl ho
    · simpa [Side.elim] using h.1
    · simpa [Side.elim] using h.1
    · exact absurd rfl ho
  · have h2 := gate_isSome h.2
    rw [adapt2_f, PairAt.one_ne s w _ (Ne.symm hs)] at h2
    simpa using h2

omit [Sem S] in
/-- An older reader changes no map at an orientation whose caller side is `false`. -/
theorem extendRead_f_of_c' {V M : Type} (c : Codec V M) (r : V → Option V) :
    ∀ o : Orient, o.c = false → (c.extendRead r).f o = c.f o :=
  Orient.both (P := fun o => o.c = false → (c.extendRead r).f o = c.f o)
    (fun _ => rfl) (fun h => nomatch h)

/-- **A refinement over a term below the top, over a wider term below the top, admits more.** -/
theorem LeK.refine_top {k : Nat} {c c' : Mean.C S.sig} {qV qA : Mean.V (B := S.sig) → Bool}
    (h : LeK (o := o) k c c') (hs : Sub c (Syn.top (S := S))) (hs' : Sub c' (Syn.top (S := S))) :
    LeK (o := o) k (refine2 c qV qA) (refine2 c' qV qA) := by
  intro v hv hA
  rw [refine2_f_isSome, Bool.and_eq_true] at hA ⊢
  refine ⟨hA.1, ?_⟩
  unfold gate at hA ⊢
  cases hc : c.f o v with
  | none => rw [hc] at hA; exact nomatch hA.2
  | some y =>
    rw [hc] at hA
    have hy : y = v := by have := hs o v y hc; simp only [Syn.top, idCodec] at this; exact (Option.some.inj this).symm
    have hc' := h v hv (by rw [hc]; rfl)
    obtain ⟨y', hy'⟩ := Option.isSome_iff_exists.mp hc'
    have hyv : y' = v := by have := hs' o v y' hy'; simp only [Syn.top, idCodec] at this; exact (Option.some.inj this).symm
    rw [hy']
    subst hy hyv
    exact hA.2

/-- **A refinement whose view keeps only the predicate of the caller side admits more.** -/
theorem LeK.refine_view {k : Nat} {c c' : Mean.C S.sig} {p : S.sig.P false} {pA : S.sig.P true}
    (h : LeK (o := o) k c c') :
    LeK (o := o) k (refine2 c (Mean.eval false p) (Mean.eval true pA))
      (refine2 c' (Mean.eval false (bif o.c then Mean.truth false else p))
        (Mean.eval true (bif o.c then pA else Mean.truth true))) := by
  intro v hv hA
  have hci := h v hv (refine2_acc hA)
  rw [refine2_f_isSome, Bool.and_eq_true] at hA ⊢
  rcases orient_cases o with ⟨hc, hs⟩ | ⟨hc, hs⟩
  · rw [hc] at hA ⊢; rw [hs]
    refine ⟨hA.1, ?_⟩
    simp only [Side.elim, cond_false]
    rw [show Mean.eval (B := S.sig) true (Mean.truth true) = fun _ => true from funext (Mean.eval_truth true),
      gate_true]
    exact hci
  · rw [hc] at hA ⊢; rw [hs]
    refine ⟨hA.1, ?_⟩
    simp only [Side.elim, cond_true]
    rw [show Mean.eval (B := S.sig) false (Mean.truth false) = fun _ => true from funext (Mean.eval_truth false),
      gate_true]
    exact hci

/-- The entry codec of an object at a name is the declared codec, or the codec of the open block. -/
theorem entryCodec_mk {fs : Finset String} {md : {x // x ∈ fs} → SlotMode S.sig}
    (c : {x // x ∈ fs} → Mean.C S.sig) (rc : Option (Mean.C S.sig)) (key : String) :
    entryCodec (⟨fs, fun x => mkField (md x) (c x)⟩ : MapOf _) rc key =
      if h : key ∈ fs then some (c ⟨key, h⟩) else rc := by
  unfold entryCodec
  rcases Decidable.em (key ∈ fs) with h | h
  · rw [MapOf.at_of_mem (m := ⟨fs, _⟩) ⟨key, h⟩, dif_pos h]
    simp only
    cases md ⟨key, h⟩ <;> rfl
  · rw [MapOf.at_none (m := ⟨fs, _⟩) h, dif_neg h]

/-- **An object over slots that accept more accepts more**, one depth down. -/
theorem LeK.obj (F : MapA (Mean.V (B := S.sig)) (Mean.Mem (B := S.sig)) Mean.mem Mean.d) {k : Nat}
    {fs : Finset String} {md : {x // x ∈ fs} → SlotMode S.sig} {w : Fin 2}
    {c c' : {x // x ∈ fs} → Mean.C S.sig} {f f' : Fin w → Mean.C S.sig}
    (hc : ∀ x, LeK (o := o) k (c x) (c' x)) (hf : ∀ p, LeK (o := o) k (f p) (f' p)) :
    LeK (o := o) (k + 1) (objectCodec F.toSummand ⟨fs, fun x => mkField (md x) (c x)⟩ (restOf w f))
      (objectCodec F.toSummand ⟨fs, fun x => mkField (SlotMode.view o (md x)) (c' x)⟩ (restOf w f')) := by
  intro v hv hA
  rw [objectCodec_f] at hA ⊢
  cases hx : F.p.out v with
  | none => rw [hx] at hA; exact nomatch hA
  | some m =>
    rw [hx] at hA
    simp only [Option.bind_some, Option.isSome_map] at hA ⊢
    obtain ⟨hAb, hEn⟩ := objAt_isSome.mp hA
    refine objAt_isSome.mpr ⟨fun key hk hkm => ?_, fun key => ?_⟩
    · have h1 := hAb key hk hkm
      rw [MapOf.at_of_mem (m := ⟨fs, fun x => mkField (md x) (c x)⟩) ⟨key, hk⟩] at h1
      rw [MapOf.at_of_mem (m := ⟨fs, fun x => mkField (SlotMode.view o (md x)) (c' x)⟩) ⟨key, hk⟩]
      simp only at h1 ⊢
      cases hm : md ⟨key, hk⟩ with
      | req => rw [hm] at h1; exact nomatch h1
      | opt => rfl
      | fill v₀ =>
        rw [hm] at h1
        rcases orient_cases o with ⟨hoc, -⟩ | ⟨hoc, -⟩
        · simp only [mkField, absentOf, hoc, cond_false] at h1; exact nomatch h1
        · simp only [SlotMode.view, hoc, cond_true, mkField, absentOf]; rfl
    · have h1 := hEn key
      have hd := F.d_lt m key
      rw [← F.p.into_out hx] at hd
      rw [entryCodec_mk] at h1 ⊢
      split at h1
      · next hk =>
        rw [dif_pos hk]
        simp only [Option.bind_some] at h1 ⊢
        exact hc _ _ (by omega) h1
      · next hk =>
        rw [dif_neg hk]
        match w, f, f', hf, h1 with
        | ⟨0, _⟩, _, _, _, h1 => exact nomatch h1
        | ⟨1, _⟩, f, f', hf, h1 =>
          simp only [restOf, rcOf, Option.bind_some] at h1 ⊢
          exact hf _ _ (by omega) h1

section Entries
variable [TopLaws S] {N : Nat} (d : Closed S.sig N)

/-- **One node of the view admits what the node admits**, from its arguments: at the depth of the
    node for a `keep` node and a wall, and one depth down for a container. -/
theorem node_le {op : TOp S.sig} {a : op.Pos → Graph S.sig N} {k : Nat}
    (hk : op.kind ≠ .down → ∀ p, LeK (o := o) k (mng τ (Closed.toG τ d) (a p))
      (mng τ (Closed.viewToG τ o d) (viewG d.graph o (a p))))
    (hd : ∀ k', k = k' + 1 → op.kind = .down → ∀ p, LeK (o := o) k' (mng τ (Closed.toG τ d) (a p))
      (mng τ (Closed.viewToG τ o d) (viewG d.graph o (a p)))) :
    LeK (o := o) k (mng τ (Closed.toG τ d) (.node op a))
      (mng τ (Closed.viewToG τ o d) (viewG d.graph o (.node op a))) := by
  cases op with
  | prim g => exact fun _ _ h => h
  | opaq => exact fun _ _ h => h
  | never => exact fun _ _ h => h
  | union m => exact LeK.union (hk (fun h => nomatch h))
  | held s k₀ ks =>
    intro v hv hA
    have := held1_acc hA
    show ((mng τ (Closed.viewToG τ o d) (bif s == o.c then viewG d.graph o (a false)
      else viewG d.graph o (a true))).f o v).isSome = true
    cases s <;> cases hc : o.c
    · exact hk (fun h => nomatch h) false v hv (this.1 hc.symm)
    · exact hk (fun h => nomatch h) true v hv (this.2 fun h => by rw [hc] at h; exact nomatch h)
    · exact hk (fun h => nomatch h) true v hv (this.2 fun h => by rw [hc] at h; exact nomatch h)
    · exact hk (fun h => nomatch h) false v hv (this.1 hc.symm)
  | legacy r =>
    intro v hv hA
    simp only [viewG]
    rcases orient_cases o with ⟨hc, -⟩ | ⟨hc, -⟩
    · rw [hc]; simp only [cond_false]
      have h1 : ((mng τ (Closed.toG τ d) (a ())).f o v).isSome = true := by
        have := hA
        rw [show mng τ (Closed.toG τ d) (.node (.legacy r) a) =
          (mng τ (Closed.toG τ d) (a ())).extendRead (Mean.read r) from rfl,
          extendRead_f_of_c' _ _ o hc] at this
        exact this
      exact hk (fun h => nomatch h) () v hv h1
    · rw [hc]; rfl
  | refine p pA =>
    simp only [viewG]
    split
    · next hb =>
      exact LeK.refine_top (hk (fun h => nomatch h) ()) (sub_of_belowTop (Closed.toG τ d) hb)
        (sub_of_belowTop (Closed.viewToG τ o d) (belowTop_viewG d.graph o _))
    · exact LeK.refine_view (hk (fun h => nomatch h) ())
  | set =>
    cases k with
    | zero => exact LeK.zero _ _
    | succ k =>
      intro v hv hA
      show ((TOp.run τ .set fun p => mng τ (Closed.viewToG τ o d) (viewG d.graph o (a p))).f o v).isSome = true
      have hA' : ((TOp.run τ .set fun p => mng τ (Closed.toG τ d) (a p)).f o v).isSome = true := hA
      simp only [TOp.run] at hA' ⊢
      split at hA'
      · next L hL =>
        exact LeK.set L hL (hd k rfl rfl _) (sub_of_belowTop (Closed.viewToG τ o d)
          (belowTop_viewG d.graph o _)) v hv hA'
      · exact nomatch hA'
  | list n s m =>
    cases k with
    | zero => exact LeK.zero _ _
    | succ k =>
      intro v hv hA
      show ((TOp.run τ (.list n s m) fun p => mng τ (Closed.viewToG τ o d) (viewG d.graph o (a p))).f o v).isSome = true
      have hA' : ((TOp.run τ (.list n s m) fun p => mng τ (Closed.toG τ d) (a p)).f o v).isSome = true := hA
      simp only [TOp.run] at hA' ⊢
      split at hA'
      · next L hL =>
        have hp := hd k rfl rfl
        refine LeK.list L (forall₂_ofFn fun p => hp _) ?_ (forall₂_ofFn fun p => hp _) v hv hA'
        match s with
        | ⟨0, _⟩ => exact .none
        | ⟨1, _⟩ => exact .some (hp _)
      · exact nomatch hA'
  | obj fs md w =>
    cases k with
    | zero => exact LeK.zero _ _
    | succ k =>
      intro v hv hA
      show ((TOp.run τ (.obj fs (fun x => SlotMode.view o (md x)) w) fun p =>
        mng τ (Closed.viewToG τ o d) (viewG d.graph o (a p))).f o v).isSome = true
      have hA' : ((TOp.run τ (.obj fs md w) fun p => mng τ (Closed.toG τ d) (a p)).f o v).isSome = true := hA
      simp only [TOp.run] at hA' ⊢
      split at hA'
      · next F hF =>
        have hp := hd k rfl rfl
        exact LeK.obj F (fun x => hp (.inl x)) (fun q => hp (.inr q)) v hv hA'
      · exact nomatch hA'

omit [TopLaws S] in
/-- Acceptance from one codec to another reads the two codecs through their maps only. -/
theorem LeK.congr {k : Nat} {c c' c₁ c₁' : Mean.C S.sig} (h₁ : c.f = c₁.f) (h₂ : c'.f = c₁'.f)
    (h : LeK (o := o) k c c') : LeK (o := o) k c₁ c₁' := fun x hx hA => by
  rw [← h₂]; exact h x hx (by rw [h₁]; exact hA)

/-- The view of a term admits what the term admits, where each entry of the term does. -/
theorem lem_all : ∀ (t : Graph S.sig N) (k : Nat),
    (∀ j, t.lv (TSig S.sig) j = true → LeK (o := o) k ((Closed.toG τ d).e j) ((Closed.viewToG τ o d).e j)) →
      LeK (o := o) k (mng τ (Closed.toG τ d) t) (mng τ (Closed.viewToG τ o d) (viewG d.graph o t)) := by
  intro t
  induction t with
  | leaf j => exact fun k h => h j (decide_eq_true rfl)
  | node op a ih =>
    intro k h
    exact node_le d (fun _ p => ih p k fun j hj => h j (Flat.lv_node.mpr ⟨p, hj⟩))
      (fun k' hk' _ p => ih p k' fun j hj => (h j (Flat.lv_node.mpr ⟨p, hj⟩)).mono (by omega))

/-- …one depth deeper, where each entry at an unguarded leaf or below a wall is one depth deeper. -/
theorem lem_u {k : Nat} (hall : ∀ j, LeK (o := o) k ((Closed.toG τ d).e j) ((Closed.viewToG τ o d).e j)) :
    ∀ t : Graph S.sig N, (∀ j, t.ulv (TSig S.sig) j = true ∨ t.wlv (TSig S.sig) j = true →
      LeK (o := o) (k + 1) ((Closed.toG τ d).e j) ((Closed.viewToG τ o d).e j)) →
        LeK (o := o) (k + 1) (mng τ (Closed.toG τ d) t) (mng τ (Closed.viewToG τ o d) (viewG d.graph o t)) := by
  intro t
  induction t with
  | leaf j => exact fun h => h j (Or.inl (decide_eq_true rfl))
  | node op a ih =>
    intro h
    refine node_le d (fun hnd p => ?_) (fun k' hk' _ p => ?_)
    · rcases TOp.kind_cases op with hk | hk | hk
      · exact ih p fun j hj => h j (hj.elim
          (fun hu => Or.inl (Flat.ulv_node_iff.mpr ⟨hk, p, hu⟩))
          (fun hw => Or.inr (Flat.wlv_node.mpr (Or.inr ⟨fun h' => absurd (hk.symm.trans h') (fun e => nomatch e), p, hw⟩))))
      · exact absurd hk hnd
      · exact lem_all d (a p) (k + 1) fun j hj => h j (Or.inr (Flat.wlv_node.mpr (Or.inl ⟨hk, p, hj⟩)))
    · obtain rfl : k' = k := by omega
      exact lem_all d (a p) _ fun j _ => hall j

/-- **Each entry of the view admits what the entry admits**, by induction on the depth, and at one
    depth by induction on the entry: an unguarded edge and a leaf below a wall lower the entry. -/
theorem view_entries : ∀ k (i : Fin N),
    LeK (o := o) k ((Closed.toG τ d).e i) ((Closed.viewToG τ o d).e i) := by
  intro k
  induction k with
  | zero => exact fun _ => LeK.zero _ _
  | succ k ih =>
    have key : ∀ m (i : Fin N), i.val < m →
        LeK (o := o) (k + 1) ((Closed.toG τ d).e i) ((Closed.viewToG τ o d).e i) := by
      intro m
      induction m with
      | zero => exact fun i hi => absurd hi (Nat.not_lt_zero _)
      | succ m ihm =>
        intro i hi
        have hT := lem_u d ih (d.graph i) fun j hj => ihm j (by
          rcases hj with hj | hj
          · have := (SSys.order d).1 i j hj; omega
          · exact absurd hj (by rw [(SSys.order d).2 i j]; decide))
        exact LeK.congr ((Closed.toG τ d).fix i).symm ((Closed.viewToG τ o d).fix i).symm hT
    exact fun i => key (i.val + 1) i (Nat.lt_succ_self _)

end Entries

/-- **A closed codec accepts no datum that a view apart from its view accepts**, where the
    decision separates the two views at the orientation. -/
theorem view_apart {S : Syn} [Sem S] [Leaf S.sig] [Shapes S] [TopLaws S]
    {τ : (s : Bool) → TableAt S.sig s} {o : Orient} (laws : Laws S o) {NL NR : Nat}
    {dL : Closed S.sig NL} {dR : Closed S.sig NR} {rL : Fin NL} {rR : Fin NR}
    (h : decG (viewSys dL.graph o) (viewSys dR.graph o) (fuel NL NR) []
      (.leaf rL) (.leaf rR) = true) {v : Mean.V (B := S.sig)}
    (hL : (((Closed.viewToG τ o dL).e rL).f o v).isSome = true) :
    ((Closed.meaning τ dR rR).f o v).isSome = false := by
  have hap := apart_of_AB (fun k => decG_sound (dL := Closed.viewToG τ o dL) (dR := Closed.viewToG τ o dR)
    laws _ [] (.leaf rL) (.leaf rR) h k fun _ hq => nomatch hq) v
  cases h2 : ((Closed.meaning τ dR rR).f o v).isSome
  · rfl
  have h3 : ((((Closed.viewToG τ o dL).e rL).f o v).isSome &&
      (((Closed.viewToG τ o dR).e rR).f o v).isSome) = false := hap
  rw [hL, view_entries dR _ rR v (Nat.le_refl _) h2] at h3
  exact nomatch h3

/-- **Two closed codecs whose views at an orientation are disjoint accept no common datum there.** -/
theorem views_apart {S : Syn} [Sem S] [Leaf S.sig] [Shapes S] [TopLaws S]
    {τ : (s : Bool) → TableAt S.sig s} {o : Orient} (laws : Laws S o) {NL NR : Nat}
    {dL : Closed S.sig NL} {dR : Closed S.sig NR} {rL : Fin NL} {rR : Fin NR}
    (h : decG (viewSys dL.graph o) (viewSys dR.graph o) (fuel NL NR) []
      (.leaf rL) (.leaf rR) = true) (v : Mean.V (B := S.sig)) :
    (((Closed.meaning τ dL rL).f o v).isSome && ((Closed.meaning τ dR rR).f o v).isSome) = false := by
  cases h1 : ((Closed.meaning τ dL rL).f o v).isSome
  · rfl
  exact (Bool.true_and _).trans (view_apart laws h (view_entries dL _ rL v (Nat.le_refl _) h1))


end ViewLe

end Calculus.Alg.Scoped
