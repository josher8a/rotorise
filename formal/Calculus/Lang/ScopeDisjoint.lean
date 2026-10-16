import Calculus.Lang.Scope
import Calculus.Lang.Universe
import Calculus.Alg.Rows

/-!
# Disjointness over the graph of a closed codec

`Scoped.disjoint` decides that two closed codecs share no datum. The decision reads the flat graph
of each closed codec, with one row per operation of the left operand. Below a guard, the decision
assumes a pair of entries while it compares the two bodies. At an unguarded position, the decision
unfolds an entry. A fuel bounds the walk, so the recursion is structural, and an empty fuel answers
`false`.

`walk` is the one walk of both relations. A `Row` holds the cases of a relation, one for each
operation of the left operand. The walk holds the table, the fuel and the test below a guard
(`pairX`), and the row reads the walk at the next fuel. `rowSpecG` is the row of disjointness, and
`decG` is the walk of that row. `Scoped.compat` is the walk of the row of agreement.

`Scoped.disjoint_sound` states the soundness: where the decision answers `true`, no datum of any
depth is accepted by both meanings at the orientation. The pairs that the walk visits form one
relation (`Vis`). Each visited pair passes the rows at tests that the relation holds, or is two
entries whose bodies the relation holds (`vis_postW`). The proof is a rule induction on a big-step
derivation of the left answer (`Eval`), with no fuel, no table and no step index. A derivation goes
one level down into the datum only at a container. The fixed point of the system has a derivation
at each input (`eval_of_mng`), because the system has no cycle of unguarded edges. The laws of a universe enter
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

/-- Every pair of two aligned rows passes the test. -/
def allZipT {X Y : Type} (T : X → Y → Bool) : List X → List Y → Bool
  | x :: xs, y :: ys => T x y && allZipT T xs ys
  | _, _ => true

/-- **The aligned rows of two list shapes**, one pair of rows at each common length. A shape with
    no spread has one length, and the pair is absent where the other shape refuses that length.
    Two spreading shapes both admit a length from `lo` up. The middle positions pair the two
    spreads from the length `hi + 1` up, and each longer row re-spreads the row at `hi + 1`, so the
    lengths `lo` to `hi + 1` reach every pair of positions. -/
def alignedRows {X Y : Type} (fpre : List X) (fsp : Option X) (fsuf : List X)
    (pre₂ : List Y) (sp₂ : Option Y) (suf₂ : List Y) : List (List X × List Y) :=
  match fsp, sp₂ with
  | some f, some c =>
      (List.range' (max (fpre.length + fsuf.length) (pre₂.length + suf₂.length))
          (max fpre.length pre₂.length + max fsuf.length suf₂.length + 2
            - max (fpre.length + fsuf.length) (pre₂.length + suf₂.length))).filterMap fun n =>
        match rowOfG fpre (some f) fsuf n, rowOfG pre₂ (some c) suf₂ n with
        | some fs, some us => some (fs, us)
        | _, _ => none
  | none, _ =>
      match rowOfG pre₂ sp₂ suf₂ (fpre.length + fsuf.length) with
      | some us => [(fpre ++ fsuf, us)]
      | none => []
  | some f, none =>
      match rowOfG fpre (some f) fsuf (pre₂.length + suf₂.length) with
      | some fs => [(fs, pre₂ ++ suf₂)]
      | none => []

/-- **A property of the aligned rows**: the test `p` holds for the two rows at each common length.
    A shape with no spread has one length, and a length that the other shape refuses has no test. -/
def alignedAll {X Y : Type} (p : List X → List Y → Bool) (fpre : List X) (fsp : Option X)
    (fsuf : List X) (pre₂ : List Y) (sp₂ : Option Y) (suf₂ : List Y) : Bool :=
  (alignedRows fpre fsp fsuf pre₂ sp₂ suf₂).all fun r => p r.1 r.2

/-- The aligned rows of a shape with no spread on the left: one length. -/
theorem alignedAll_none {X Y : Type} (p : List X → List Y → Bool) (fpre fsuf : List X)
    (pre₂ : List Y) (sp₂ : Option Y) (suf₂ : List Y) :
    alignedAll p fpre none fsuf pre₂ sp₂ suf₂ =
      match rowOfG pre₂ sp₂ suf₂ (fpre.length + fsuf.length) with
      | some us => p (fpre ++ fsuf) us
      | none => true := by
  unfold alignedAll alignedRows
  rcases h : rowOfG pre₂ sp₂ suf₂ (fpre.length + fsuf.length) with _ | us <;> simp [h]

/-- The aligned rows of a spreading shape beside a shape with no spread: one length. -/
theorem alignedAll_some_none {X Y : Type} (p : List X → List Y → Bool) (fpre : List X) (f : X)
    (fsuf : List X) (pre₂ suf₂ : List Y) :
    alignedAll p fpre (some f) fsuf pre₂ none suf₂ =
      match rowOfG fpre (some f) fsuf (pre₂.length + suf₂.length) with
      | some fs => p fs (pre₂ ++ suf₂)
      | none => true := by
  unfold alignedAll alignedRows
  rcases h : rowOfG fpre (some f) fsuf (pre₂.length + suf₂.length) with _ | fs <;> simp [h]

/-- The aligned rows of two spreading shapes: every length from `lo` to `hi + 1`. -/
theorem alignedAll_some_some {X Y : Type} (p : List X → List Y → Bool) (fpre : List X) (f : X)
    (fsuf : List X) (pre₂ : List Y) (c : Y) (suf₂ : List Y) :
    alignedAll p fpre (some f) fsuf pre₂ (some c) suf₂ =
      (List.range' (max (fpre.length + fsuf.length) (pre₂.length + suf₂.length))
          (max fpre.length pre₂.length + max fsuf.length suf₂.length + 2
            - max (fpre.length + fsuf.length) (pre₂.length + suf₂.length))).all fun n =>
        match rowOfG fpre (some f) fsuf n, rowOfG pre₂ (some c) suf₂ n with
        | some fs, some us => p fs us
        | _, _ => true := by
  unfold alignedAll alignedRows
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true, List.mem_filterMap]
  constructor
  · intro h n hn
    rcases h1 : rowOfG fpre (some f) fsuf n with _ | fs
    · rfl
    rcases h2 : rowOfG pre₂ (some c) suf₂ n with _ | us
    · rfl
    · exact h (fs, us) ⟨n, hn, by simp [h1, h2]⟩
  · rintro h r ⟨n, hn, hr⟩
    have hn' := h n hn
    rcases h1 : rowOfG fpre (some f) fsuf n with _ | fs
    · simp [h1] at hr
    rcases h2 : rowOfG pre₂ (some c) suf₂ n with _ | us
    · simp [h1, h2] at hr
    · simp only [h1, h2, Option.some.injEq] at hr hn'
      subst hr; exact hn'

/-- **Two list shapes**: one disjoint position in the aligned rows at each common length. -/
def listRowG {X : Type} (fpre : List (X → Bool)) (fsp : Option (X → Bool))
    (fsuf : List (X → Bool)) (pre₂ : List X) (sp₂ : Option X) (suf₂ : List X) : Bool :=
  alignedAll anyZipG fpre fsp fsuf pre₂ sp₂ suf₂

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

/-- The positions of a list node, at any codomain. -/
def listPartsX {X : Type} {a : Nat} {s : Fin 2} {b : Nat}
    (g : TOp.Pos (B := B) (.list a s b) → X) : List X × Option X × List X :=
  (List.ofFn fun p => g (.inl p), optOf s (fun p => g (.inr (.inl p))),
    List.ofFn fun p => g (.inr (.inr p)))

/-- The test of the open block of a left object: `true` where the object has no block. -/
def blockX {fs : Finset String} {md : {x // x ∈ fs} → SlotMode B} :
    (w : Fin 2) → ((TOp.obj fs md w).Pos → Graph B NR → Bool) → Graph B NR → Bool
  | ⟨0, _⟩, _ => fun _ => true
  | ⟨1, _⟩, g => g (.inr ⟨0, Nat.one_pos⟩)

/-- **A pair of positions below a guard.** A pair of entries is looked up or assumed, and spends
    one fuel. Any other pair has a closed side, which holds no leaf, so no cycle passes through
    the pair. The pair runs `self`, the row at the same fuel. Both relations read this test. -/
def pairX (prev : Tbl NL NR → Graph B NL → Graph B NR → Bool) (A : Tbl NL NR)
    (t : Graph B NL) (self : Graph B NR → Bool) : Graph B NR → Bool := fun y =>
  match t, y with
  | .leaf i, .leaf j => A.any (fun p => decide (p.1 = i) && decide (p.2 = j)) ||
      prev ((i, j) :: A) (sL i) (sR j)
  | _, _ => self y

/-- **A row of the walk**, one for each relation. The row reads the restart `rs`, which is the
    walk at the table. At a node, the row reads for each position the test `self` and the test
    `kid` below a guard. -/
structure Row (sL : Fin NL → Graph B NL) (sR : Fin NR → Graph B NR) where
  leaf : (Graph B NL → Graph B NR → Bool) → Fin NL → Graph B NR → Bool
  node : (Graph B NL → Graph B NR → Bool) → (op : TOp B) → (a : op.Pos → Graph B NL) →
    (op.Pos → Graph B NR → Bool) → (op.Pos → Graph B NR → Bool) → Graph B NR → Bool

/-- **The row at a table**, structural on the left term. The walk supplies the pair test. -/
def goW (R : Row sL sR) (prev : Tbl NL NR → Graph B NL → Graph B NR → Bool) (A : Tbl NL NR) :
    Graph B NL → Graph B NR → Bool
  | .leaf j => R.leaf (prev A) j
  | .node op a => R.node (prev A) op a (fun p => goW R prev A (a p))
      (fun p => pairX (sL := sL) (sR := sR) prev A (a p) (goW R prev A (a p)))

/-- **The walk.** The table, the fuel and the pair test live here. Each unfolding of an entry and
    each pair of entries below a guard spends one fuel. -/
def walk (R : Row sL sR) : Nat → Tbl NL NR → Graph B NL → Graph B NR → Bool
  | 0 => fun _ _ _ => false
  | n + 1 => goW R (walk R n)

variable (sL sR)

/-- **The row of disjointness**, one case for each operation of the left operand. -/
def rowSpecG : Row sL sR where
  leaf rs j y := rs (sL j) y
  node rs op a self kid y := match op, a, self, kid with
    | .never, _, _, _ => true
    | .held s k ks, a, _, _ => rightC sR (rs (.node (.held s k ks) a)) (fun _ => false) y
    | .legacy r, a, _, _ => rightC sR (rs (.node (.legacy r) a)) (fun _ => false) y
    | .opaq, a, _, _ => rightC sR (rs (.node .opaq a)) (fun _ => false) y
    | .refine _ _, _, self, _ => self () y
    | .union m, _, self, _ => (List.finRange m).all fun p => self p y
    | .prim g, a, _, _ => rightC sR (rs (.node (.prim g) a)) (famPrimG g) y
    | .set, a, _, kid => rightC sR (rs (.node .set a)) (famSetG (kid ())) y
    | .list n s m, a, _, kid => rightC sR (rs (.node (.list n s m) a))
        (famListG (listPartsX (B := B) kid).1 (listPartsX (B := B) kid).2.1 (listPartsX (B := B) kid).2.2) y
    | .obj fs md s, a, _, kid => rightC sR (rs (.node (.obj fs md s) a))
        (famObjG (md := md) (fun k => kid (.inl k)) (blockX (md := md) s kid)) y

/-- **One row per operation of the left operand**, with `prev` as the walk at the next fuel. -/
def rowG (prev : Tbl NL NR → Graph B NL → Graph B NR → Bool) (A : Tbl NL NR) :
    Graph B NL → Graph B NR → Bool :=
  goW (rowSpecG sL sR) prev A

/-- **The fuel of a walk over two closed codecs** of `NL` and `NR` entries. -/
def fuel (NL NR : Nat) : Nat := (NL * NR + 1) * (NL + NR + 2)

/-- **The walk at a fuel**, the walk of the row of disjointness. -/
def decG : Nat → Tbl NL NR → Graph B NL → Graph B NR → Bool := walk (rowSpecG sL sR)

variable {sL sR}

/-- The case of `rowG` at an entry. -/
theorem rowG_leaf (prev : Tbl NL NR → Graph B NL → Graph B NR → Bool) (A : Tbl NL NR) (j : Fin NL)
    (y : Graph B NR) : rowG sL sR prev A (.leaf j) y = prev A (sL j) y := rfl

/-- The case of `rowG` at the bottom. -/
theorem rowG_never (prev : Tbl NL NR → Graph B NL → Graph B NR → Bool) (A : Tbl NL NR)
    (a : (TSig B).Pos TOp.never → Graph B NL) (y : Graph B NR) :
    rowG sL sR prev A (.node .never a) y = true := rfl

/-- The case of `rowG` at a refinement. -/
theorem rowG_refine (prev : Tbl NL NR → Graph B NL → Graph B NR → Bool) (A : Tbl NL NR)
    {p : B.P false} {pA : B.P true} (a : (TSig B).Pos (TOp.refine p pA) → Graph B NL) (y : Graph B NR) :
    rowG sL sR prev A (.node (.refine p pA) a) y = rowG sL sR prev A (a ()) y := rfl

/-- The case of `rowG` at a union. -/
theorem rowG_union (prev : Tbl NL NR → Graph B NL → Graph B NR → Bool) (A : Tbl NL NR) {m : Nat}
    (a : (TSig B).Pos (TOp.union m) → Graph B NL) (y : Graph B NR) :
    rowG sL sR prev A (.node (.union m) a) y =
      (List.finRange m).all fun p => rowG sL sR prev A (a p) y := rfl

/-- The case of `rowG` at a primitive. -/
theorem rowG_prim (prev : Tbl NL NR → Graph B NL → Graph B NR → Bool) (A : Tbl NL NR) (g : B.Ground)
    (a : (TSig B).Pos (TOp.prim g) → Graph B NL) (y : Graph B NR) :
    rowG sL sR prev A (.node (.prim g) a) y =
      rightC sR (prev A (.node (.prim g) a)) (famPrimG g) y := rfl

/-- The case of `rowG` at the top. -/
theorem rowG_opaq (prev : Tbl NL NR → Graph B NL → Graph B NR → Bool) (A : Tbl NL NR)
    (a : (TSig B).Pos TOp.opaq → Graph B NL) (y : Graph B NR) :
    rowG sL sR prev A (.node .opaq a) y = rightC sR (prev A (.node .opaq a)) (fun _ => false) y := rfl

/-- The case of `rowG` at a `held`. -/
theorem rowG_held (prev : Tbl NL NR → Graph B NL → Graph B NR → Bool) (A : Tbl NL NR) {s : Bool}
    {k : B.G s × Bool} {ks : List (B.G s × Bool)}
    (a : (TSig B).Pos (TOp.held s k ks) → Graph B NL) (y : Graph B NR) :
    rowG sL sR prev A (.node (.held s k ks) a) y =
      rightC sR (prev A (.node (.held s k ks) a)) (fun _ => false) y := rfl

/-- The case of `rowG` at a `legacy`. -/
theorem rowG_legacy (prev : Tbl NL NR → Graph B NL → Graph B NR → Bool) (A : Tbl NL NR)
    {r : B.R} (a : (TSig B).Pos (TOp.legacy r) → Graph B NL) (y : Graph B NR) :
    rowG sL sR prev A (.node (.legacy r) a) y =
      rightC sR (prev A (.node (.legacy r) a)) (fun _ => false) y := rfl

/-- The case of `rowG` at a set. -/
theorem rowG_set (prev : Tbl NL NR → Graph B NL → Graph B NR → Bool) (A : Tbl NL NR)
    (a : (TSig B).Pos TOp.set → Graph B NL) (y : Graph B NR) :
    rowG sL sR prev A (.node .set a) y = rightC sR (prev A (.node .set a)) (famSetG
      (pairX (sL := sL) (sR := sR) prev A (a ()) (rowG sL sR prev A (a ())))) y := rfl

/-- The case of `rowG` at a list. -/
theorem rowG_list (prev : Tbl NL NR → Graph B NL → Graph B NR → Bool) (A : Tbl NL NR) {n m : Nat}
    {s : Fin 2} (a : (TSig B).Pos (TOp.list n s m) → Graph B NL) (y : Graph B NR) :
    rowG sL sR prev A (.node (.list n s m) a) y =
      rightC sR (prev A (.node (.list n s m) a)) (famListG
        (listPartsX (B := B) (fun p => pairX (sL := sL) (sR := sR) prev A (a p) (rowG sL sR prev A (a p)))).1
        (listPartsX (B := B) (fun p => pairX (sL := sL) (sR := sR) prev A (a p) (rowG sL sR prev A (a p)))).2.1
        (listPartsX (B := B) (fun p => pairX (sL := sL) (sR := sR) prev A (a p) (rowG sL sR prev A (a p)))).2.2)
        y := rfl

/-- The case of `rowG` at an object. -/
theorem rowG_obj (prev : Tbl NL NR → Graph B NL → Graph B NR → Bool) (A : Tbl NL NR)
    {fs : Finset String} {md : {x // x ∈ fs} → SlotMode B} {s : Fin 2}
    (a : (TSig B).Pos (TOp.obj fs md s) → Graph B NL) (y : Graph B NR) :
    rowG sL sR prev A (.node (.obj fs md s) a) y =
      rightC sR (prev A (.node (.obj fs md s) a)) (famObjG (md := md)
        (fun k => pairX (sL := sL) (sR := sR) prev A (a (.inl k)) (rowG sL sR prev A (a (.inl k))))
        (blockX (md := md) s fun p => pairX (sL := sL) (sR := sR) prev A (a p) (rowG sL sR prev A (a p)))) y :=
  rfl

/-- **The cases of `rowG`**, as one tactic. -/
macro "simp_rowG" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [rowG_leaf, rowG_never, rowG_refine, rowG_union, rowG_prim, rowG_opaq,
    rowG_held, rowG_legacy, rowG_set, rowG_list, rowG_obj] $[$loc]?)

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
  · rw [listRowG, alignedAll_none] at h
    rw [rowOfG_none_eq] at h₁
    split at h₁
    · next hn =>
      simp only [Option.some.injEq] at h₁; subst h₁
      rw [show fpre.length + fsuf.length = n by omega, h₂] at h
      exact rowsAp_of_anyZip (forall₂_append hp hf) h
    · exact nomatch h₁
  · cases sp₂ with
    | none =>
      rw [listRowG, alignedAll_some_none] at h
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
      rw [listRowG, alignedAll_some_some] at h
      have hn₁ := rowOfG_isSome_len' h₁
      have hn₂ := rowOfG_isSome_len' h₂
      generalize hP : max fpre.length pre₂.length = P' at h
      generalize hS : max fsuf.length suf₂.length = S' at h
      have hall := List.all_eq_true.mp h
      rcases Nat.lt_or_ge (P' + S') n with hlt | hle
      · have hm := hall (P' + S') (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
        obtain ⟨fs, hfs⟩ := rowOfG_total (pre := fpre) (suf := fsuf) (c := f) (n := P' + S')
          (by omega)
        obtain ⟨us, hus⟩ := rowOfG_total (pre := pre₂) (suf := suf₂) (c := c) (n := P' + S')
          (by omega)
        rw [hfs, hus] at hm
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
        rcases anyZipG_take_drop P' hm with ha | ha
        · rw [List.append_assoc, List.append_assoc]
          exact RowsAp.append_left (by simp; omega)
            (rowsAp_of_anyZip (List.forall₂_take P' hF) ha)
        · exact RowsAp.append_right (by simp; omega)
            (rowsAp_of_anyZip (List.forall₂_drop P' hF) ha)
      · have hm := hall n (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
        obtain ⟨fs, hfs⟩ := rowOfG_total (pre := fpre) (suf := fsuf) (c := f) (n := n) (by omega)
        rw [hfs, h₂] at hm
        exact rowsAp_of_anyZip
          (rowOfG_forall₂ (R := SoundG P Q) hp (Or.inr ⟨t, f, rfl, rfl, htf⟩) hf h₁ hfs) hm

/-- Two aligned rows stand in the relation where the test accepts each aligned pair. -/
theorem forall₂_of_allZipT {X Y : Type} {Ag : X → Y → Prop} {T : X → Y → Bool}
    (hT : ∀ x y, T x y = true → Ag x y) :
    ∀ {r₁ : List X} {r₂ : List Y}, r₁.length = r₂.length → allZipT T r₁ r₂ = true →
      List.Forall₂ Ag r₁ r₂
  | [], [], _, _ => .nil
  | [], _ :: _, hl, _ => (Nat.succ_ne_zero _ hl.symm).elim
  | _ :: _, [], hl, _ => (Nat.succ_ne_zero _ hl).elim
  | x :: r₁, y :: r₂, hl, h => by
      simp only [allZipT, Bool.and_eq_true] at h
      exact .cons (hT x y h.1) (forall₂_of_allZipT hT (Nat.succ.inj hl) h.2)

/-- One related pair of two rows cut at the same index. -/
theorem forall₂_cut {X Y : Type} {R : X → Y → Prop} {x : X} {y : Y} {B : List X} {D : List Y} :
    ∀ {A : List X} {C : List Y}, A.length = C.length →
      List.Forall₂ R (A ++ x :: B) (C ++ y :: D) → R x y
  | [], [], _, h => (List.forall₂_cons.mp h).1
  | _ :: _, _ :: _, hl, h =>
      forall₂_cut (Nat.succ.inj hl) (List.forall₂_cons.mp h).2
  | [], _ :: _, hl, _ => (Nat.succ_ne_zero _ hl.symm).elim
  | _ :: _, [], hl, _ => (Nat.succ_ne_zero _ hl).elim

/-- **Two list shapes agree at each common length**, where the test accepts each aligned pair of
    the rows. Two spreading shapes read the rows from `lo` to `hi + 1`. The row at a longer length
    re-spreads the row at `hi`, and the row at `hi + 1` pairs the two spreads. -/
theorem alignedAll_forall₂ {X Y : Type} {Ag : X → Y → Prop} {T : X → Y → Bool}
    (hT : ∀ x y, T x y = true → Ag x y) {pre suf : List X} {sp : Option X}
    {pre₂ suf₂ : List Y} {sp₂ : Option Y}
    (h : alignedAll (allZipT T) pre sp suf pre₂ sp₂ suf₂ = true) :
    ∀ n r₁ r₂, rowOfG pre sp suf n = some r₁ → rowOfG pre₂ sp₂ suf₂ n = some r₂ →
      List.Forall₂ Ag r₁ r₂ := by
  intro n r₁ r₂ h₁ h₂
  cases sp with
  | none =>
    rw [alignedAll_none] at h
    rw [rowOfG_none_eq] at h₁
    split at h₁
    · next hn =>
      simp only [Option.some.injEq] at h₁; subst h₁
      rw [← hn, h₂] at h
      exact forall₂_of_allZipT hT (by rw [rowOfG_length h₂, List.length_append]; omega) h
    · exact nomatch h₁
  | some t =>
    cases sp₂ with
    | none =>
      rw [alignedAll_some_none] at h
      rw [rowOfG_none_eq] at h₂
      split at h₂
      · next hn =>
        simp only [Option.some.injEq] at h₂; subst h₂
        rw [← hn, h₁] at h
        exact forall₂_of_allZipT hT (by rw [rowOfG_length h₁, List.length_append]; omega) h
      · exact nomatch h₂
    | some c =>
      rw [alignedAll_some_some] at h
      have hn₁ := rowOfG_isSome_len' h₁
      have hn₂ := rowOfG_isSome_len' h₂
      generalize hP : max pre.length pre₂.length = P' at h
      generalize hS : max suf.length suf₂.length = S' at h
      have hall := List.all_eq_true.mp h
      have key : ∀ m, m < P' + S' + 2 → pre.length + suf.length ≤ m →
          pre₂.length + suf₂.length ≤ m →
          ∃ a₁ a₂, rowOfG pre (some t) suf m = some a₁ ∧ rowOfG pre₂ (some c) suf₂ m = some a₂ ∧
            List.Forall₂ Ag a₁ a₂ := by
        intro m hm1 hm2 hm3
        have hmem := hall m (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
        obtain ⟨a₁, ha₁⟩ := rowOfG_total (pre := pre) (suf := suf) (c := t) (n := m) (by omega)
        obtain ⟨a₂, ha₂⟩ := rowOfG_total (pre := pre₂) (suf := suf₂) (c := c) (n := m) (by omega)
        rw [ha₁, ha₂] at hmem
        exact ⟨a₁, a₂, ha₁, ha₂, forall₂_of_allZipT hT
          (by rw [rowOfG_length ha₁, rowOfG_length ha₂]) hmem⟩
      rcases Nat.lt_or_ge n (P' + S') with hlt | hge
      · obtain ⟨a₁, a₂, e₁, e₂, hF⟩ := key n (by omega) (by omega) (by omega)
        rw [h₁] at e₁; rw [h₂] at e₂
        cases e₁; cases e₂
        exact hF
      · obtain ⟨b₁, b₂, eb₁, eb₂, hB⟩ := key (P' + S') (by omega) (by omega) (by omega)
        obtain ⟨c₁, c₂, ec₁, ec₂, hC⟩ := key (P' + S' + 1) (by omega) (by omega) (by omega)
        have rc₁ := rowOfG_respread (P := P') (S := S') (n := P' + S' + 1) (by omega) (by omega)
          (by omega) eb₁ ec₁
        have rc₂ := rowOfG_respread (P := P') (S := S') (n := P' + S' + 1) (by omega) (by omega)
          (by omega) eb₂ ec₂
        have hl₁ := rowOfG_length eb₁
        have hl₂ := rowOfG_length eb₂
        have htc : Ag t c := by
          rw [rc₁, rc₂, show P' + S' + 1 - P' - S' = 1 by omega] at hC
          simp only [List.replicate_succ, List.replicate_zero, List.append_assoc,
            List.singleton_append, List.nil_append] at hC
          exact forall₂_cut (by simp only [List.length_take]; omega) hC
        have r₁' := rowOfG_respread (P := P') (S := S') (n := n) (by omega) (by omega) hge eb₁ h₁
        have r₂' := rowOfG_respread (P := P') (S := S') (n := n) (by omega) (by omega) hge eb₂ h₂
        rw [r₁', r₂']
        exact forall₂_append (forall₂_append (List.forall₂_take P' hB)
          (forall₂_replicate htc _)) (List.forall₂_drop P' hB)

end RowsGen

/-! ## The pairs that a walk visits -/

section Visited
variable {B : Sig} {NL NR : Nat} (sL : Fin NL → Graph B NL) (sR : Fin NR → Graph B NR)

/-- A Bool relation whose pairs all hold the Prop relation. -/
def SubR {X Y : Type} (Rb : X → Y → Bool) (R : X → Y → Prop) : Prop := ∀ a b, Rb a b = true → R a b

section Walk
variable (W : Nat → Tbl NL NR → Graph B NL → Graph B NR → Bool)

/-- **A pair that a relation justifies**: a walk that answers `true` from a table whose pairs the
    relation holds, or two entries whose bodies the relation holds. -/
def Just (S : Graph B NL → Graph B NR → Prop) (x : Graph B NL) (y : Graph B NR) : Prop :=
  (∃ m A, W m A x y = true ∧ ∀ p ∈ A, S (.leaf p.1) (.leaf p.2)) ∨
    ∃ i j, x = .leaf i ∧ y = .leaf j ∧ S (sL i) (sR j)

/-- **The visited relation**: the pairs of some relation that justifies each of its pairs. -/
def Vis (x : Graph B NL) (y : Graph B NR) : Prop :=
  ∃ S, (∀ a b, S a b → Just sL sR W S a b) ∧ S x y

/-- A larger relation justifies each pair that a relation justifies. -/
theorem Just.mono {S T : Graph B NL → Graph B NR → Prop} (h : ∀ a b, S a b → T a b)
    {x : Graph B NL} {y : Graph B NR} : Just sL sR W S x y → Just sL sR W T x y
  | .inl ⟨m, A, hw, hA⟩ => .inl ⟨m, A, hw, fun p hp => h _ _ (hA p hp)⟩
  | .inr ⟨i, j, hx, hy, hs⟩ => .inr ⟨i, j, hx, hy, h _ _ hs⟩

/-- **A relation that the visited relation justifies is visited.** -/
theorem vis_of {T : Graph B NL → Graph B NR → Prop}
    (hT : ∀ a b, T a b → Just sL sR W (fun a b => Vis sL sR W a b ∨ T a b) a b)
    {x : Graph B NL} {y : Graph B NR} (h : T x y) : Vis sL sR W x y :=
  ⟨fun a b => Vis sL sR W a b ∨ T a b, fun a b hab => by
    rcases hab with ⟨S, hS, hab⟩ | hab
    · exact Just.mono sL sR W (fun a b h => Or.inl ⟨S, hS, h⟩) (hS a b hab)
    · exact hT a b hab, Or.inr h⟩

/-- A walk that answers `true` from a visited table visits its root. -/
theorem vis_walk {m : Nat} {A : Tbl NL NR} {x : Graph B NL} {y : Graph B NR}
    (h : W m A x y = true) (hA : ∀ p ∈ A, Vis sL sR W (.leaf p.1) (.leaf p.2)) :
    Vis sL sR W x y :=
  vis_of sL sR W (T := fun a b => a = x ∧ b = y)
    (fun _ _ hab => by
      obtain ⟨rfl, rfl⟩ := hab
      exact .inl ⟨m, A, h, fun p hp => Or.inl (hA p hp)⟩) ⟨rfl, rfl⟩

/-- A walk from the empty table visits its root. -/
theorem vis_root {m : Nat} {x : Graph B NL} {y : Graph B NR} (h : W m [] x y = true) :
    Vis sL sR W x y :=
  vis_walk sL sR W h fun _ hp => nomatch hp

/-- **A walk of two bodies that assumes their entries visits the two entries.** -/
theorem vis_pair {m : Nat} {A : Tbl NL NR} {i : Fin NL} {j : Fin NR}
    (h : W m ((i, j) :: A) (sL i) (sR j) = true)
    (hA : ∀ p ∈ A, Vis sL sR W (.leaf p.1) (.leaf p.2)) : Vis sL sR W (.leaf i) (.leaf j) :=
  vis_of sL sR W (T := fun a b => (a = .leaf i ∧ b = .leaf j) ∨ (a = sL i ∧ b = sR j))
    (fun a b hab => by
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .inr ⟨i, j, rfl, rfl, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
      · refine .inl ⟨m, _, h, fun p hp => ?_⟩
        rcases List.mem_cons.mp hp with rfl | hp
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
        · exact Or.inl (hA p hp))
    (Or.inl ⟨rfl, rfl⟩)

end Walk

/-- The optional spread of a list, mapped at the positions, is the mapped optional spread. -/
theorem optOf_mapX {X Y : Type} (g : X → Y) : ∀ (s : Fin 2) (f : Fin s → X),
    optOf s (fun p => g (f p)) = (optOf s f).map g
  | ⟨0, _⟩, _ => rfl
  | ⟨1, _⟩, _ => rfl

/-- The parts of a list node at a test of each position are the tests of the parts. -/
theorem listPartsX_eq {N n m : Nat} {s : Fin 2} {X : Type}
    (a : (TOp.list n s m (B := B)).Pos → Graph B N) (T : Graph B N → X) :
    listPartsX (fun p => T (a p)) =
      ((listParts a).1.map T, (listParts a).2.1.map T, (listParts a).2.2.map T) := by
  simp only [listPartsX, listParts, List.map_ofFn, Function.comp_def]
  rw [optOf_mapX T s (fun p => a (.inr (.inl p)))]

variable [Leaf B] {sL sR}

/-- **The row with two tests**: the restart `Rr`, and the test `Rc` of a child below a guard. -/
def rowT (R : Row sL sR) (Rr Rc : Graph B NL → Graph B NR → Bool) : Graph B NL → Graph B NR → Bool
  | .leaf j => R.leaf Rr j
  | .node op a => R.node Rr op a (fun p => rowT R Rr Rc (a p)) (fun p => Rc (a p))

omit [Leaf B] in
/-- **The row of the walk is the row with two tests**: the walk at the table, and the pair test
    at the row of the same fuel. -/
theorem goW_eq_rowT (R : Row sL sR) (prev : Tbl NL NR → Graph B NL → Graph B NR → Bool)
    (A : Tbl NL NR) :
    ∀ x y, goW R prev A x y =
      rowT R (prev A) (fun a => pairX (sL := sL) (sR := sR) prev A a (goW R prev A a)) x y := by
  intro x
  induction x with
  | leaf j => intro y; rfl
  | node op a ih =>
    intro y
    have h : ∀ p, goW R prev A (a p) =
        rowT R (prev A) (fun a => pairX (sL := sL) (sR := sR) prev A a (goW R prev A a)) (a p) :=
      fun p => funext (ih p)
    exact congrArg (fun F => R.node (prev A) op a F
      (fun p => pairX (sL := sL) (sR := sR) prev A (a p) (goW R prev A (a p))) y) (funext h)

/-- **Post-fixed up to the unfolding of two entries**: each pair passes the row at two tests that
    the relation holds, or is two entries whose bodies the relation holds. -/
def PostT (R : Row sL sR) (S : Graph B NL → Graph B NR → Prop) : Prop :=
  ∀ x y, S x y → (∃ Rr Rc : Graph B NL → Graph B NR → Bool,
    SubR Rr S ∧ SubR Rc S ∧ rowT R Rr Rc x y = true) ∨
    ∃ i j, x = .leaf i ∧ y = .leaf j ∧ S (sL i) (sR j)

omit [Leaf B] in
/-- **A pair below a guard that the walk answers is visited**: a pair of entries through the
    table, and any other pair through the walk at one more fuel. -/
theorem vis_pairXW (R : Row sL sR) {k : Nat} {A : Tbl NL NR}
    (hA : ∀ p ∈ A, Vis sL sR (walk R) (.leaf p.1) (.leaf p.2)) :
    ∀ a b, pairX (sL := sL) (sR := sR) (walk R k) A a (goW R (walk R k) A a) b = true →
      Vis sL sR (walk R) a b
  | .leaf i, .leaf j, hab => by
    simp only [pairX, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at hab
    rcases hab with ⟨p, hp, h1, h2⟩ | hab
    · subst h1 h2; exact hA p hp
    · exact vis_pair sL sR _ hab hA
  | .leaf _, .node _ _, hab => vis_walk sL sR _ (m := k + 1) hab hA
  | .node _ _, _, hab => vis_walk sL sR _ (m := k + 1) hab hA

omit [Leaf B] in
/-- **The visited relation of a walk is post-fixed up to unfolding**, for each row. -/
theorem vis_postW (R : Row sL sR) : PostT R (Vis sL sR (walk R)) := by
  rintro x y ⟨S, hS, hxy⟩
  rcases hS x y hxy with ⟨m, A, h, hA⟩ | ⟨i, j, rfl, rfl, hs⟩
  · have hA' : ∀ p ∈ A, Vis sL sR (walk R) (.leaf p.1) (.leaf p.2) := fun p hp => ⟨S, hS, hA p hp⟩
    cases m with
    | zero => exact nomatch h
    | succ k =>
      refine Or.inl ⟨walk R k A,
        fun a => pairX (sL := sL) (sR := sR) (walk R k) A a (goW R (walk R k) A a),
        fun a b hab => vis_walk sL sR _ hab hA', vis_pairXW R hA', ?_⟩
      rw [← goW_eq_rowT]; exact h
  · exact Or.inr ⟨i, j, rfl, rfl, S, hS, hs⟩

/-- **The visited relation of `decG` is post-fixed up to unfolding.** -/
theorem vis_postG : PostT (rowSpecG sL sR) (Vis sL sR (decG sL sR)) := vis_postW (rowSpecG sL sR)

end Visited

/-! ## A term with no leaf -/

section NoLeaf
variable {B : Sig} {N : Nat}

/-- A term with no leaf at any position. -/
def NoLeaf (t : Graph B N) : Prop := ∀ j, t.lv (TSig B) j = false

/-- Each child of a term with no leaf has no leaf. -/
theorem noLeaf_child {op : TOp B} {a : op.Pos → Graph B N} (h : NoLeaf (.node op a))
    (p : op.Pos) : NoLeaf (a p) :=
  fun j => Bool.eq_false_iff.mpr fun h' =>
    Bool.false_ne_true ((h j).symm.trans (Flat.lv_node.mpr ⟨p, h'⟩))

/-- An entry is a leaf. -/
theorem not_noLeaf_leaf (j : Fin N) : ¬ NoLeaf (.leaf j : Graph B N) := fun h => by
  have := h j
  simp [Flat.lv] at this

/-- The bottom has no leaf. -/
theorem noLeaf_never (a' : (TSig B).Pos TOp.never → Graph B N) : NoLeaf (.node .never a' : Graph B N) :=
  fun j => by simp [Flat.lv, TSig, TOp.pos]

end NoLeaf

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

/-- **A pointwise step relation**: the relation `Φ` holds between the two outputs at each datum of
    a smaller depth, at the orientation. Apartness and agreement below a depth are two instances. -/
def PW (Φ : Option (Mean.V (B := S.sig)) → Option (Mean.V (B := S.sig)) → Prop) (k : Nat)
    (c c' : Mean.C S.sig) : Prop :=
  ∀ v, Mean.d (B := S.sig) v < k → Φ (c.f o v) (c'.f o v)

variable {τ o}

variable {Φ : Option (Mean.V (B := S.sig)) → Option (Mean.V (B := S.sig)) → Prop}

/-- Any two codecs are related below the depth one, because every datum has a depth of at least
    one. -/
theorem PW.one (c c' : Mean.C S.sig) : PW o Φ 1 c c' :=
  fun v hv => absurd hv (Nat.not_lt.mpr (Mean.d_pos v))

variable (o) in
/-- **Apart below a depth**: no datum of a smaller depth is accepted by both codecs at the
    orientation. -/
def AB (k : Nat) (c c' : Mean.C S.sig) : Prop :=
  ∀ v, Mean.d (B := S.sig) v < k → ((c.f o v).isSome && (c'.f o v).isSome) = false

/-- A codec cut at a depth. -/
def trunc (d : Nat) (c : Mean.C S.sig) : Mean.C S.sig where
  T := c.T
  μ := c.μ
  f o x := if Mean.d (B := S.sig) x ≤ d then c.f o x else none

/-- A codec cut at a depth agrees with the codec at that depth. -/
theorem trunc_agree (d : Nat) (c : Mean.C S.sig) : AgreeLe Mean.d d (trunc d c) c :=
  ⟨fun o x hx => by simp only [trunc, if_pos hx]⟩

/-- **A container is related below one more depth** where its positions, cut at the depth, give
    two related containers at each datum: the step reads the positions one layer down. -/
theorem PW.down {op op' : TOp S.sig} (hk : op.kind = .down) (hk' : op'.kind = .down)
    {a : op.Pos → Mean.C S.sig} {b : op'.Pos → Mean.C S.sig} {j : Nat}
    (h : ∀ v, Φ ((TOp.run τ op fun p => trunc j (a p)).f o v)
      ((TOp.run τ op' fun q => trunc j (b q)).f o v)) :
    PW o Φ (j + 2) (TOp.run τ op a) (TOp.run τ op' b) := by
  have ha := (TStep_lawful τ).down op hk j a (fun p => trunc j (a p))
    fun p => (trunc_agree j (a p)).symm
  have hb := (TStep_lawful τ).down op' hk' j b (fun q => trunc j (b q))
    fun q => (trunc_agree j (b q)).symm
  intro x hx
  have e1 : (TOp.run τ op a).f o x = (TOp.run τ op fun p => trunc j (a p)).f o x :=
    ha.f o x (by omega)
  have e2 : (TOp.run τ op' b).f o x = (TOp.run τ op' fun q => trunc j (b q)).f o x :=
    hb.f o x (by omega)
  rw [e1, e2]
  exact h x

/-- **The cut of two related codecs is related at each datum**, where the relation holds of two
    absences. -/
theorem PW.trunc (hnn : Φ none none) {j : Nat} {c c' : Mean.C S.sig} (h : PW o Φ (j + 1) c c') :
    ∀ v, Φ ((trunc j c).f o v) ((trunc j c').f o v) := fun v => by
  simp only [Calculus.Alg.Scoped.trunc]
  split
  · exact h v (by omega)
  · exact hnn

/-- A container is apart below one more depth where its positions, cut at the depth, give two
    apart containers. -/
theorem AB.down {op op' : TOp S.sig} (hk : op.kind = .down) (hk' : op'.kind = .down)
    {a : op.Pos → Mean.C S.sig} {b : op'.Pos → Mean.C S.sig} {j : Nat}
    (h : ∀ v, (((TOp.run τ op fun p => trunc j (a p)).f o v).isSome &&
      ((TOp.run τ op' fun q => trunc j (b q)).f o v).isSome) = false) :
    AB o (j + 2) (TOp.run τ op a) (TOp.run τ op' b) :=
  PW.down (Φ := fun a b => (a.isSome && b.isSome) = false) hk hk' h

/-- Two codecs apart below one more depth give two cut codecs that are apart. -/
theorem AB.trunc {j : Nat} {c c' : Mean.C S.sig} (h : AB o (j + 1) c c') :
    ∀ v, (((trunc j c).f o v).isSome && ((trunc j c').f o v).isSome) = false :=
  PW.trunc (Φ := fun a b => (a.isSome && b.isSome) = false) rfl h

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

variable {N NR : Nat}

/-! ### The derivation of an answer -/

/-- **The big-step derivation of an answer** of a graph term at the fixed point of a system. A
    container reads its positions at a smaller depth of the datum only. A wall reads the fixed
    point, and carries a derivation of each child that has no leaf. -/
inductive Eval (d : GSys τ N) :
    Graph S.sig N → Orient → Mean.V (B := S.sig) → Option (Mean.V (B := S.sig)) → Prop
  | leaf {i o v r} : Eval d (d.sys i) o v r → Eval d (.leaf i) o v r
  | prim {g a o v} : Eval d (.node (TOp.prim g) a) o v ((Mean.ground g).f o v)
  | opaq {a o v} : Eval d (.node TOp.opaq a) o v (some v)
  | never {a o v} : Eval d (.node TOp.never a) o v none
  | refine {p pA a o v r} : Eval d (a ()) o v r →
      Eval d (.node (TOp.refine p pA) a) o v
        (if Side.elim (Mean.eval false p) (Mean.eval true pA) o.c v then
          r.bind fun y => if Side.elim (Mean.eval false p) (Mean.eval true pA) o.s y then some y
            else none
        else none)
  | unionNil {a o v} : Eval d (.node (TOp.union 0) a) o v none
  | unionHead {m o v w} {a : Fin (m + 1) → Graph S.sig N} : Eval d (a 0) o v (some w) →
      Eval d (.node (TOp.union (m + 1)) a) o v (some w)
  | unionTail {m o v r} {a : Fin (m + 1) → Graph S.sig N} : Eval d (a 0) o v none →
      Eval d (.node (TOp.union m) fun p : Fin m => a p.succ) o v r →
      Eval d (.node (TOp.union (m + 1)) a) o v r
  | down {op a o v} (hk : TOp.kind op = .down) (C : op.Pos → Mean.C S.sig)
      (hC : ∀ p o' x, Mean.d x < Mean.d v → Eval d (a p) o' x ((C p).f o' x)) :
      Eval d (.node op a) o v ((TOp.run τ op C).f o v)
  | wall {op a o v} (hk : TOp.kind op = .wall)
      (hC : ∀ p, NoLeaf (a p) → ∀ o' x, Eval d (a p) o' x ((mng τ d (a p)).f o' x)) :
      Eval d (.node op a) o v ((TOp.run τ op fun p => mng τ d (a p)).f o v)

/-- A union's map is its first option's answer, else the union of the rest. -/
theorem mng_union_succ (d : GSys τ N) {m : Nat} (a : Fin (m + 1) → Graph S.sig N) (o : Orient)
    (v : Mean.V (B := S.sig)) :
    (mng τ d (.node (TOp.union (m + 1)) a)).f o v =
      if ((mng τ d (a 0)).f o v).isSome then (mng τ d (a 0)).f o v
      else (mng τ d (.node (TOp.union m) fun p : Fin m => a p.succ)).f o v := by
  show select (List.ofFn fun p => mng τ d (a p)) (·.f o) v = _
  rw [List.ofFn_succ, select_cons]
  rfl

/-- **A derivation computes the map of the fixed point.** -/
theorem mng_of_eval (d : GSys τ N) {t o v r} (h : Eval d t o v r) : (mng τ d t).f o v = r := by
  induction h with
  | leaf _ ih => rw [mng_leaf]; exact ih
  | prim => rfl
  | opaq => rfl
  | never => rfl
  | refine _ ih => subst ih; rfl
  | unionNil => rfl
  | unionHead _ ih => rw [mng_union_succ, ih]; rfl
  | unionTail _ _ ih₀ ih => rw [mng_union_succ, ih₀]; exact ih
  | @down op a o v hk C _ ih =>
    have hd := Mean.d_pos (B := S.sig) v
    have hag := (TStep_lawful τ).down op hk (Mean.d (B := S.sig) v - 1) (fun p => mng τ d (a p)) C
      fun p => ⟨fun o' x hx => ih p o' x (by omega)⟩
    exact hag.f o v (by omega)
  | wall _ _ => rfl

/-- The union case of completeness, by induction on the number of options. -/
theorem eval_union (d : GSys τ N) (o : Orient) (v : Mean.V (B := S.sig)) :
    ∀ (m : Nat) (a : Fin m → Graph S.sig N), (∀ p, Eval d (a p) o v ((mng τ d (a p)).f o v)) →
      Eval d (.node (TOp.union m) a) o v ((mng τ d (.node (TOp.union m) a)).f o v)
  | 0, _, _ => Eval.unionNil
  | m + 1, a, ih => by
    rw [mng_union_succ]
    cases h : (mng τ d (a 0)).f o v with
    | none =>
      have h0 := ih 0; rw [h] at h0
      exact Eval.unionTail h0 (eval_union d o v m _ fun p => ih p.succ)
    | some w =>
      have h0 := ih 0; rw [h] at h0
      exact Eval.unionHead h0

/-- **A term with no leaf has a derivation at each input**, by induction on the term. -/
theorem eval_noLeaf (d : GSys τ N) : ∀ t : Graph S.sig N, NoLeaf t →
    ∀ o v, Eval d t o v ((mng τ d t).f o v)
  | .leaf j, h => absurd (h j) (by simp [Flat.lv])
  | .node op a, h => fun o v => by
    have ih : ∀ p o' x, Eval d (a p) o' x ((mng τ d (a p)).f o' x) :=
      fun p => eval_noLeaf d (a p) (noLeaf_child h p)
    have hdown : TOp.kind op = .down → Eval d (.node op a) o v ((mng τ d (.node op a)).f o v) :=
      fun hk => Eval.down hk (fun p => mng τ d (a p)) fun p o' x _ => ih p o' x
    cases op with
    | prim g => exact Eval.prim
    | opaq => exact Eval.opaq
    | never => exact Eval.never
    | refine p pA => exact Eval.refine (ih () o v)
    | union m => exact eval_union d o v m a fun p => ih p o v
    | set => exact hdown rfl
    | list _ _ _ => exact hdown rfl
    | obj _ _ _ => exact hdown rfl
    | held _ _ _ => exact Eval.wall rfl fun p _ => ih p
    | legacy _ => exact Eval.wall rfl fun p _ => ih p

/-- **The fixed point has a derivation at each input.** The length of an unguarded walk and the
    depth of the datum are the measure: the system has no cycle of unguarded edges. -/
theorem eval_of_mng (d : GSys τ N) : ∀ t o v, Eval d t o v ((mng τ d t).f o v) := by
  have hK : ∀ j, ¬ WalkFrom (TSig S.sig) d.sys N j := fun j hw => d.noCycle (cycle_of_walk hw)
  suffices H : ∀ D k (t : Graph S.sig N), (∀ j, t.ulv (TSig S.sig) j = true →
      ¬ WalkFrom (TSig S.sig) d.sys k j) →
      ∀ o v, Mean.d (B := S.sig) v ≤ D → Eval d t o v ((mng τ d t).f o v) from
    fun t o v => H _ _ t (fun j _ => hK j) o v le_rfl
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ihD =>
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ihk =>
  intro t
  induction t with
  | leaf j =>
    intro hb o v hv
    have hj := hb j (by simp [Flat.ulv])
    have e := congrFun (congrFun (mng_leaf d j) o) v
    rw [e]
    cases k with
    | zero => exact absurd ⟨fun _ => j, rfl, fun _ ht => absurd ht (Nat.not_lt_zero _)⟩ hj
    | succ k' =>
      exact Eval.leaf (ihk k' (Nat.lt_succ_self _) (d.sys j)
        (fun j' h' hw => hj (walk_cons h' hw)) o v hv)
  | node op a iha =>
    intro hb o v hv
    have hb' : TOp.kind op = .keep → ∀ p j, (a p).ulv (TSig S.sig) j = true →
        ¬ WalkFrom (TSig S.sig) d.sys k j :=
      fun hk p j h => hb j (Flat.ulv_node_iff.mpr ⟨hk, p, h⟩)
    have hdown : TOp.kind op = .down → Eval d (.node op a) o v ((mng τ d (.node op a)).f o v) :=
      fun hk => Eval.down hk (fun p => mng τ d (a p)) fun p o' x hx =>
        ihD _ (Nat.lt_of_lt_of_le hx hv) _ (a p) (fun j _ => hK j) o' x le_rfl
    have hwall : TOp.kind op = .wall → Eval d (.node op a) o v ((mng τ d (.node op a)).f o v) :=
      fun hk => Eval.wall hk fun p hp => eval_noLeaf d (a p) hp
    cases op with
    | prim g => exact Eval.prim
    | opaq => exact Eval.opaq
    | never => exact Eval.never
    | refine p pA => exact Eval.refine (iha () (hb' rfl ()) o v hv)
    | union m => exact eval_union d o v m a fun p => iha p (hb' rfl p) o v hv
    | set => exact hdown rfl
    | list _ _ _ => exact hdown rfl
    | obj _ _ _ => exact hdown rfl
    | held _ _ _ => exact hwall rfl
    | legacy _ => exact hwall rfl

omit [Sem S] in
/-- A refinement that answers gives the answer of its inner term. -/
theorem bind_some_eq {X : Type} {c : Bool} {r : Option X} {q : X → Bool} {b : X}
    (h : (if c then r.bind (fun y => if q y then some y else none) else none) = some b) :
    r = some b := by
  cases c
  · exact nomatch h
  · cases r with
    | none => exact nomatch h
    | some b' =>
      have h' : (if q b' then some b' else none) = some b := h
      cases hq : q b'
      · rw [hq] at h'; exact nomatch h'
      · rw [hq] at h'; exact h'

omit [Sem S] in
/-- Where the left side answers, apart sides leave the right side without an answer. -/
theorem none_of_apart {X : Type} {a b : Option X} {w : X} (h : (a.isSome && b.isSome) = false)
    (ha : a = some w) : b = none := by
  subst ha; cases b
  · rfl
  · exact nomatch h

/-! ### The rows of the right operand -/

/-- **The rows of the right operand, by rule induction on the right derivation**: each answer of
    a term that the rows admit holds `G`, where each answer of a term of the family holds `G`, and
    each restart lands in `P`. `disjoint` takes `G` false, and `compat` takes `G` the left answer. -/
theorem rightC_aux (dR : GSys τ NR) {o : Orient} {v : Mean.V (B := S.sig)}
    {G : Mean.V (B := S.sig) → Prop} {P : Graph S.sig NR → Prop}
    (hP : ∀ y, P y → ∃ restart fam : Graph S.sig NR → Bool, (∀ y', restart y' = true → P y') ∧
      (∀ y' b, fam y' = true → (mng τ dR y').f o v = some b → G b) ∧
      rightC dR.sys restart fam y = true) :
    ∀ {y o' v' r}, Eval dR y o' v' r → o' = o → v' = v → ∀ b, r = some b →
      ∀ restart fam : Graph S.sig NR → Bool, (∀ y', restart y' = true → P y') →
      (∀ y' b, fam y' = true → (mng τ dR y').f o v = some b → G b) →
      rightC dR.sys restart fam y = true → G b := by
  have fc : ∀ {fam : Graph S.sig NR → Bool},
      (∀ y' b, fam y' = true → (mng τ dR y').f o v = some b → G b) →
      ∀ {y b}, fam y = true → Eval dR y o v (some b) → G b := fun hfam _ _ hy he =>
    hfam _ _ hy (mng_of_eval dR he)
  intro y o' v' r h
  induction h with
  | @leaf i o' v' r h0 ih =>
    intro ho hv b hb restart fam hres hfam hy; subst ho hv hb
    simp only [rightC, Bool.or_eq_true] at hy
    rcases hy with hy | hy
    · exact fc hfam hy (Eval.leaf h0)
    · obtain ⟨r', f', h1, h2, h3⟩ := hP _ (hres _ hy)
      exact ih rfl rfl b rfl r' f' h1 h2 h3
  | @prim g a o' v' =>
    intro ho hv b hb restart fam _ hfam hy; subst ho hv; exact fc hfam hy (hb ▸ Eval.prim)
  | @opaq a o' v' =>
    intro ho hv b hb restart fam _ hfam hy; subst ho hv; cases hb; exact fc hfam hy Eval.opaq
  | never => exact fun _ _ b hb => nomatch hb
  | unionNil => exact fun _ _ b hb => nomatch hb
  | @refine p pA a o' v' r h0 ih =>
    intro ho hv b hb restart fam hres hfam hy; subst ho hv
    simp only [rightC, Bool.or_eq_true] at hy
    rcases hy with hy | hy
    · exact fc hfam hy (hb ▸ Eval.refine h0)
    · exact ih rfl rfl b (bind_some_eq hb) restart fam hres hfam hy
  | @unionHead m o' v' w a h0 ih =>
    intro ho hv b hb restart fam hres hfam hy; subst ho hv
    simp only [rightC, Bool.or_eq_true, List.all_eq_true, List.mem_finRange, true_implies] at hy
    rcases hy with hy | hy
    · exact fc hfam hy (hb ▸ Eval.unionHead h0)
    · exact ih rfl rfl b hb restart fam hres hfam (hy 0)
  | @unionTail m o' v' r a h0 h1 _ ih =>
    intro ho hv b hb restart fam hres hfam hy; subst ho hv
    simp only [rightC, Bool.or_eq_true, List.all_eq_true, List.mem_finRange, true_implies] at hy
    rcases hy with hy | hy
    · exact fc hfam hy (hb ▸ Eval.unionTail h0 h1)
    · exact ih rfl rfl b hb restart fam hres hfam (by
        simp only [rightC, Bool.or_eq_true, List.all_eq_true, List.mem_finRange, true_implies]
        exact Or.inr fun p => hy p.succ)
  | @down op a o' v' hk C hC _ =>
    intro ho hv b hb restart fam _ hfam hy; subst ho hv
    cases op with
    | set => exact fc hfam hy (hb ▸ Eval.down hk C hC)
    | list _ _ _ => exact fc hfam hy (hb ▸ Eval.down hk C hC)
    | obj _ _ _ => exact fc hfam hy (hb ▸ Eval.down hk C hC)
    | _ => exact nomatch hk
  | @wall op a o' v' hk hC _ =>
    intro ho hv b hb restart fam _ hfam hy; subst ho hv
    cases op with
    | held _ _ _ => exact fc hfam hy (hb ▸ Eval.wall hk hC)
    | legacy _ => exact fc hfam hy (hb ▸ Eval.wall hk hC)
    | _ => exact nomatch hk

/-- Each answer of a term that the rows admit holds `G`. -/
theorem rightC_mng (dR : GSys τ NR) {o : Orient} {v : Mean.V (B := S.sig)}
    {G : Mean.V (B := S.sig) → Prop} {P : Graph S.sig NR → Prop}
    (hP : ∀ y, P y → ∃ restart fam : Graph S.sig NR → Bool, (∀ y', restart y' = true → P y') ∧
      (∀ y' b, fam y' = true → (mng τ dR y').f o v = some b → G b) ∧
      rightC dR.sys restart fam y = true)
    {restart fam : Graph S.sig NR → Bool} (hres : ∀ y', restart y' = true → P y')
    (hfam : ∀ y' b, fam y' = true → (mng τ dR y').f o v = some b → G b) :
    ∀ y, rightC dR.sys restart fam y = true → ∀ b, (mng τ dR y).f o v = some b → G b := by
  intro y hy b hb
  have he := eval_of_mng dR y o v
  rw [hb] at he
  exact rightC_aux dR hP he rfl rfl b rfl restart fam hres hfam hy

/-- The family and the restarts of the rows admit no answer: `G` false. -/
theorem rightC_noneP (dR : GSys τ NR) {o : Orient} {v : Mean.V (B := S.sig)}
    {P : Graph S.sig NR → Prop}
    (hP : ∀ y, P y → ∃ restart fam : Graph S.sig NR → Bool, (∀ y', restart y' = true → P y') ∧
      (∀ y', fam y' = true → (mng τ dR y').f o v = none) ∧ rightC dR.sys restart fam y = true)
    {restart fam : Graph S.sig NR → Bool} (hres : ∀ y', restart y' = true → P y')
    (hfam : ∀ y', fam y' = true → (mng τ dR y').f o v = none) :
    ∀ y, rightC dR.sys restart fam y = true → (mng τ dR y).f o v = none := by
  have cv : ∀ {fam : Graph S.sig NR → Bool}, (∀ y', fam y' = true → (mng τ dR y').f o v = none) →
      ∀ y' b, fam y' = true → (mng τ dR y').f o v = some b → False := fun h y' b hy hb => by
    rw [h y' hy] at hb; exact nomatch hb
  intro y hy
  cases hm : (mng τ dR y).f o v with
  | none => rfl
  | some b =>
    exact absurd (rightC_mng dR (G := fun _ => False) (fun y' h' => by
      obtain ⟨r, f, h1, h2, h3⟩ := hP y' h'
      exact ⟨r, f, h1, cv h2, h3⟩) hres (cv hfam) y hy b hm) id

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

variable {NL : Nat} {dL : GSys τ NL} {dR : GSys τ NR}

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
/-- **A list codec accepts a datum through the row of its shape.** -/
theorem list_acc (L : ListA (Mean.V (B := S.sig)) (Mean.Mem (B := S.sig)) Mean.mem Mean.d)
    {pre suf : List (Mean.C S.sig)} {sp : Option (Mean.C S.sig)} {v : Mean.V (B := S.sig)}
    (h : ((listCodec L.toSummand pre sp suf).f o v).isSome = true) :
    ∃ xs, L.p.out v = some xs ∧ ∃ row, rowOfG pre sp suf xs.length = some row ∧
      zipP (row.map fun c u => (c.f o u).isSome) xs = true := by
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
      exact ⟨row, by rw [← slotsL_eq_rowOfG]; exact hs,
        zipP_of_traverse row xs (slotsL_length _ _ _ _ _ hs) h⟩

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
theorem optCases {X Y : Type} {R : X → Y → Prop} {f : X → Y} (sp : Option X)
    (h : ∀ t ∈ sp, R t (f t)) :
    (sp = none ∧ sp.map f = none) ∨ ∃ t g, sp = some t ∧ sp.map f = some g ∧ R t g := by
  cases sp with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some t => exact Or.inr ⟨t, f t, rfl, rfl, h t rfl⟩

omit [Leaf S.sig] [Shapes S] in
/-- The list codec of a list node of a graph, over the meanings of its positions. -/
theorem mng_list {N : Nat} (d : GSys τ N) {n m : Nat} {s' : Fin 2}
    (a : (TOp.list n s' m (B := S.sig)).Pos → Graph S.sig N) :
    mng τ d (.node (.list n s' m) a) = TOp.run τ (.list n s' m) (fun p => mng τ d (a p)) := rfl

omit [Leaf S.sig] [Shapes S] in
/-- The codec row of a list node is the map of the term row through a codec of each term. -/
theorem rowOfG_listParts {N : Nat} (φ : Graph S.sig N → Mean.C S.sig) {n m : Nat} {s' : Fin 2}
    (a : (TOp.list n s' m (B := S.sig)).Pos → Graph S.sig N) (len : Nat) :
    rowOfG (List.ofFn fun p => φ (a (.inl p))) (optOf s' fun p => φ (a (.inr (.inl p))))
        (List.ofFn fun p => φ (a (.inr (.inr p)))) len =
      (rowOfG (listParts a).1 (listParts a).2.1 (listParts a).2.2 len).map (List.map φ) := by
  rw [← rowOfG_map]
  simp only [listParts, List.map_ofFn, ← optOf_map]
  rfl

omit [Leaf S.sig] [Shapes S] in
/-- A member of a count of zero or one is a value of the function. -/
theorem optOf_mem {X : Type} : ∀ (s : Fin 2) (f : Fin s → X) (c : X), c ∈ optOf s f → ∃ p, f p = c
  | ⟨0, _⟩, _, _, h => nomatch h
  | ⟨1, _⟩, _, _, h => by cases h; exact ⟨_, rfl⟩

omit [Leaf S.sig] in
/-- **The list row is sound.** -/
theorem listRow_sound {test : Graph S.sig NL → Graph S.sig NR → Bool} {k : Nat}
    {n₁ m₁ : Nat} {s₁' : Fin 2} (a : (TOp.list n₁ s₁' m₁ (B := S.sig)).Pos → Graph S.sig NL)
    (htest : ∀ p y', test (a p) y' = true → AB o k (mng τ dL (a p)) (mng τ dR y'))
    (y : Graph S.sig NR)
    (h : famListG ((listParts a).1.map test) ((listParts a).2.1.map test)
        ((listParts a).2.2.map test) y = true) :
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
      cases k with
      | zero => exact PW.one (Φ := fun a b => (a.isSome && b.isSome) = false) _ _
      | succ j =>
      let φL : Graph S.sig NL → Mean.C S.sig := fun t => trunc j (mng τ dL t)
      let φR : Graph S.sig NR → Mean.C S.sig := fun t => trunc j (mng τ dR t)
      let P : Graph S.sig NL → Mean.V (B := S.sig) → Bool := fun t u => ((φL t).f o u).isSome
      let Q : Graph S.sig NR → Mean.V (B := S.sig) → Bool := fun t u => ((φR t).f o u).isSome
      have hsnd : ∀ p, SoundG P Q (a p) (test (a p)) :=
        fun p y' hy => AB.trunc (htest p y' hy)
      have hrows := listRowG_sound (P := P) (Q := Q)
        (forall₂_map_self _ fun t ht => by obtain ⟨p, rfl⟩ := List.mem_ofFn.mp ht; exact hsnd _)
        (optCases _ fun t ht => by obtain ⟨p, rfl⟩ := optOf_mem _ _ _ ht; exact hsnd _)
        (forall₂_map_self _ fun t ht => by obtain ⟨p, rfl⟩ := List.mem_ofFn.mp ht; exact hsnd _) h
      refine AB.down (τ := τ) (op := .list n₁ s₁' m₁) (op' := .list n₂ s₂' m₂)
        (a := fun p => mng τ dL (a p)) (b := fun p => mng τ dR (b p)) rfl rfl fun v => ?_
      simp only [TOp.run]
      split
      · next L hL =>
        cases h1 : ((listCodec L.toSummand (List.ofFn fun p => φL (a (.inl p)))
            (optOf s₁' fun p => φL (a (.inr (.inl p))))
            (List.ofFn fun p => φL (a (.inr (.inr p))))).f o v).isSome
        · rfl
        cases h2 : ((listCodec L.toSummand (List.ofFn fun p => φR (b (.inl p)))
            (optOf s₂' fun p => φR (b (.inr (.inl p))))
            (List.ofFn fun p => φR (b (.inr (.inr p))))).f o v).isSome
        · rfl
        obtain ⟨xs, hx, r₁, hr₁, hz₁⟩ := list_acc L h1
        obtain ⟨xs', hx', r₂, hr₂, hz₂⟩ := list_acc L h2
        rw [hx] at hx'
        cases hx'
        rw [rowOfG_listParts φL a] at hr₁
        rw [rowOfG_listParts φR b] at hr₂
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
            rw [show (fun c u => (c.f o u).isSome) ∘ φL = P from rfl,
              show (fun c u => (c.f o u).isSome) ∘ φR = Q from rfl] at *
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
theorem objRow_sound {test : Graph S.sig NL → Graph S.sig NR → Bool} {k : Nat}
    {fs : Finset String} {md : {x // x ∈ fs} → SlotMode S.sig}
    {w : Fin 2} (a : (TOp.obj fs md w).Pos → Graph S.sig NL)
    (htest : ∀ p y', test (a p) y' = true → AB o k (mng τ dL (a p)) (mng τ dR y'))
    (y : Graph S.sig NR)
    (h : famObjG (md := md) (fun k => test (a (.inl k))) (blockX (md := md) w fun p => test (a p)) y = true) :
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
        · have hab := htest _ _ hg
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
              exact htest _ _ hmw u hu
      · rfl

/-! ### A graph term below the top -/

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

variable (dL dR) in
omit [Shapes S] in
/-- **The relation from the rows**: a pair passes the rows, or is two entries whose bodies the
    relation holds, and the meaning reads an entry as its body. -/
theorem rformP {R : Graph S.sig NL → Graph S.sig NR → Prop} (hR : PostT (rowSpecG dL.sys dR.sys) R)
    {x : Graph S.sig NL} {v : Mean.V (B := S.sig)}
    (hrows : ∀ Rr Rc, SubR Rr R → SubR Rc R →
      ∀ y, rowT (rowSpecG dL.sys dR.sys) Rr Rc x y = true → (mng τ dR y).f o v = none)
    (hleaf : ∀ i j, x = .leaf i → R (dL.sys i) (dR.sys j) → (mng τ dR (dR.sys j)).f o v = none) :
    ∀ y, R x y → (mng τ dR y).f o v = none := by
  intro y hy
  rcases hR x y hy with ⟨Rr, Rc, h1, h3, h4⟩ | ⟨i, j, rfl, rfl, h⟩
  · exact hrows Rr Rc h1 h3 y h4
  · rw [congrFun (congrFun (mng_leaf dR j) o) v]; exact hleaf i j rfl h

variable (dL dR) in
/-- **Soundness by rule induction on the left derivation**, over a relation post-fixed up to
    unfolding: where the left term answers, each term that the relation pairs with the left term
    answers nothing. -/
theorem post_soundP (laws : Laws S o) {R : Graph S.sig NL → Graph S.sig NR → Prop}
    (hR : PostT (rowSpecG dL.sys dR.sys) R) :
    ∀ {x o' v r}, Eval dL x o' v r → o' = o → ∀ w, r = some w →
      (∀ Rr Rc, SubR Rr R → SubR Rc R →
        ∀ y, rowT (rowSpecG dL.sys dR.sys) Rr Rc x y = true → (mng τ dR y).f o v = none) ∧
      ∀ y, R x y → (mng τ dR y).f o v = none := by
  intro x o' v r h
  induction h with
  | @leaf i o' v r _ ih =>
    intro ho w hw
    have hrows : ∀ Rr Rc, SubR Rr R → SubR Rc R → ∀ y,
        rowT (rowSpecG dL.sys dR.sys) Rr Rc (.leaf i) y = true → (mng τ dR y).f o v = none :=
      fun Rr Rc hr _ y hy => (ih ho w hw).2 y (hr _ _ hy)
    exact ⟨hrows, rformP dL dR hR hrows fun i' j hx h => by cases hx; exact (ih ho w hw).2 _ h⟩
  | @prim g a o' v =>
    intro ho w hw; subst o'
    have hf : ∀ y', famPrimG g y' = true → (mng τ dR y').f o v = none := fun y' h' =>
      none_of_apart (famPrimG_sound laws dR (k := Mean.d (B := S.sig) v + 1)
        (fun p => mng τ dL (a p)) y' h' v (Nat.lt_succ_self _)) hw
    have hrows : ∀ Rr Rc, SubR Rr R → SubR Rc R → ∀ y,
        rowT (rowSpecG dL.sys dR.sys) Rr Rc (.node (.prim g) a) y = true → (mng τ dR y).f o v = none := by
      intro Rr Rc hr _ y hy
      simp only [rowT, rowSpecG] at hy
      refine rightC_noneP dR (P := R (.node (.prim g) a)) (fun y' h' => ?_) (hr _) hf y hy
      rcases hR _ _ h' with ⟨Rr', _, h1, _, h4⟩ | ⟨_, _, hx, _⟩
      · exact ⟨Rr' _, _, h1 _, hf, by simpa only [rowT, rowSpecG] using h4⟩
      · exact nomatch hx
    exact ⟨hrows, rformP dL dR hR hrows fun _ _ hx => nomatch hx⟩
  | @opaq a o' v =>
    intro ho w hw; subst o'
    have hrows : ∀ Rr Rc, SubR Rr R → SubR Rc R → ∀ y,
        rowT (rowSpecG dL.sys dR.sys) Rr Rc (.node .opaq a) y = true → (mng τ dR y).f o v = none := by
      intro Rr Rc hr _ y hy
      simp only [rowT, rowSpecG] at hy
      refine rightC_noneP dR (P := R (.node .opaq a)) (fun y' h' => ?_) (hr _)
        (fun _ h' => absurd h' Bool.false_ne_true) y hy
      rcases hR _ _ h' with ⟨Rr', _, h1, _, h4⟩ | ⟨_, _, hx, _⟩
      · exact ⟨Rr' _, _, h1 _, fun _ h' => absurd h' Bool.false_ne_true, by simpa only [rowT, rowSpecG] using h4⟩
      · exact nomatch hx
    exact ⟨hrows, rformP dL dR hR hrows fun _ _ hx => nomatch hx⟩
  | never => exact fun _ w hw => nomatch hw
  | @refine p pA a o' v r h0 ih =>
    intro ho w hw; subst o'
    have hrows : ∀ Rr Rc, SubR Rr R → SubR Rc R → ∀ y,
        rowT (rowSpecG dL.sys dR.sys) Rr Rc (.node (.refine p pA) a) y = true → (mng τ dR y).f o v = none :=
      fun Rr Rc hr hc y hy => (ih rfl w (bind_some_eq hw)).1 Rr Rc hr hc y hy
    exact ⟨hrows, rformP dL dR hR hrows fun _ _ hx => nomatch hx⟩
  | unionNil => exact fun _ w hw => nomatch hw
  | @unionHead m o' v w' a _ ih =>
    intro ho w hw
    have hrows : ∀ Rr Rc, SubR Rr R → SubR Rc R → ∀ y,
        rowT (rowSpecG dL.sys dR.sys) Rr Rc (.node (.union (m + 1)) a) y = true → (mng τ dR y).f o v = none := by
      intro Rr Rc hr hc y hy
      simp only [rowT, rowSpecG, List.all_eq_true, List.mem_finRange, true_implies] at hy
      exact (ih ho w hw).1 Rr Rc hr hc y (hy 0)
    exact ⟨hrows, rformP dL dR hR hrows fun _ _ hx => nomatch hx⟩
  | @unionTail m o' v r a _ _ _ ih =>
    intro ho w hw
    have hrows : ∀ Rr Rc, SubR Rr R → SubR Rc R → ∀ y,
        rowT (rowSpecG dL.sys dR.sys) Rr Rc (.node (.union (m + 1)) a) y = true → (mng τ dR y).f o v = none := by
      intro Rr Rc hr hc y hy
      simp only [rowT, rowSpecG, List.all_eq_true, List.mem_finRange, true_implies] at hy
      exact (ih ho w hw).1 Rr Rc hr hc y (by
        simp only [rowT, rowSpecG, List.all_eq_true, List.mem_finRange, true_implies]; exact fun p => hy p.succ)
    exact ⟨hrows, rformP dL dR hR hrows fun _ _ hx => nomatch hx⟩
  | @down op a o' v hk C hC ih =>
    intro ho w hw; subst o'
    have hx : (mng τ dL (.node op a)).f o v = some w := (mng_of_eval dL (Eval.down hk C hC)).trans hw
    have hAB : ∀ p y', R (a p) y' →
        AB o (Mean.d (B := S.sig) v) (mng τ dL (a p)) (mng τ dR y') := by
      intro p y' hy' u hu
      rw [mng_of_eval dL (hC p o u hu)]
      cases hcu : (C p).f o u with
      | none => rfl
      | some w' => rw [(ih p o u hu rfl w' hcu).2 y' hy']; simp
    have hrows : ∀ Rr Rc, SubR Rr R → SubR Rc R → ∀ y,
        rowT (rowSpecG dL.sys dR.sys) Rr Rc (.node op a) y = true → (mng τ dR y).f o v = none := by
      intro Rr Rc hr hc y hy
      cases op with
      | list n s m =>
        have hf : ∀ Rc : Graph S.sig NL → Graph S.sig NR → Bool, SubR Rc R → ∀ y',
            famListG ((listParts a).1.map Rc) ((listParts a).2.1.map Rc) ((listParts a).2.2.map Rc) y' = true →
            (mng τ dR y').f o v = none := fun Rc hc y' h' =>
          none_of_apart (listRow_sound a (fun p y'' h'' => hAB p y'' (hc _ _ h'')) y' h' v
            (Nat.lt_succ_self _)) hx
        simp only [rowT, rowSpecG] at hy
        rw [listPartsX_eq a Rc] at hy
        refine rightC_noneP dR (P := R (.node (.list n s m) a)) (fun y' h' => ?_) (hr _) (hf Rc hc) y hy
        rcases hR _ _ h' with ⟨Rr', Rc', h1, h3, h4⟩ | ⟨_, _, hx, _⟩
        · refine ⟨Rr' _, _, h1 _, hf Rc' h3, ?_⟩
          simp only [rowT, rowSpecG] at h4
          rw [listPartsX_eq a Rc'] at h4
          exact h4
        · exact nomatch hx
      | obj fs md s =>
        have hf : ∀ Rc : Graph S.sig NL → Graph S.sig NR → Bool, SubR Rc R → ∀ y',
            famObjG (md := md) (fun k => Rc (a (.inl k))) (blockX (md := md) s fun p => Rc (a p)) y' = true →
            (mng τ dR y').f o v = none := fun Rc hc y' h' =>
          none_of_apart (objRow_sound a (fun p y'' h'' => hAB p y'' (hc _ _ h'')) y' h' v
            (Nat.lt_succ_self _)) hx
        simp only [rowT, rowSpecG] at hy
        refine rightC_noneP dR (P := R (.node (.obj fs md s) a)) (fun y' h' => ?_) (hr _) (hf Rc hc) y hy
        rcases hR _ _ h' with ⟨Rr', Rc', h1, h3, h4⟩ | ⟨_, _, hx, _⟩
        · exact ⟨Rr' _, _, h1 _, hf Rc' h3, by simpa only [rowT, rowSpecG] using h4⟩
        · exact nomatch hx
      | set =>
        have hf : ∀ Rc : Graph S.sig NL → Graph S.sig NR → Bool, SubR Rc R → ∀ y',
            famSetG (Rc (a ())) y' = true → (mng τ dR y').f o v = none := by
          intro Rc hs' y' h'
          let a' : (TOp.set (B := S.sig)).Pos → Mean.C S.sig :=
            fun _ => trunc (Mean.d (B := S.sig) v - 1) (mng τ dL (a ()))
          have hmt : ∀ e, Rc (a ()) e = true → ∀ u,
              (((a' ()).f o u).isSome && ((mng τ dR e).f o u).isSome) = false := by
            intro e he u
            show ((if Mean.d (B := S.sig) u ≤ Mean.d (B := S.sig) v - 1 then (mng τ dL (a ())).f o u
              else none).isSome && _) = false
            split
            · next hu => exact hAB () e (hs' _ _ he) u (by have := Mean.d_pos (B := S.sig) v; omega)
            · rfl
          have hag := (TStep_lawful τ).down TOp.set rfl (Mean.d (B := S.sig) v - 1) a'
            (fun p => mng τ dL (a p)) (fun _ => trunc_agree _ _)
          have hx' : (TOp.run τ .set a').f o v = some w :=
            (hag.f o v (by have := Mean.d_pos (B := S.sig) v; omega)).trans hx
          exact none_of_apart (famSetG_sound laws dR (k := Mean.d (B := S.sig) v + 1) a' hmt y' h' v
            (Nat.lt_succ_self _)) hx'
        simp only [rowT, rowSpecG] at hy
        refine rightC_noneP dR (P := R (.node .set a)) (fun y' h' => ?_) (hr _) (hf Rc hc) y hy
        rcases hR _ _ h' with ⟨Rr', Rc', h1, h3, h4⟩ | ⟨_, _, hx, _⟩
        · exact ⟨Rr' _, _, h1 _, hf Rc' h3, by simpa only [rowT, rowSpecG] using h4⟩
        · exact nomatch hx
      | _ => exact nomatch hk
    exact ⟨hrows, rformP dL dR hR hrows fun _ _ hx => nomatch hx⟩
  | @wall op a o' v hk _ _ =>
    intro ho w hw; subst o'
    have hrows : ∀ Rr Rc, SubR Rr R → SubR Rc R → ∀ y,
        rowT (rowSpecG dL.sys dR.sys) Rr Rc (.node op a) y = true → (mng τ dR y).f o v = none := by
      intro Rr Rc hr _ y hy
      cases op with
      | held _ _ _ =>
        simp only [rowT, rowSpecG] at hy
        refine rightC_noneP dR (P := R (.node _ a)) (fun y' h' => ?_) (hr _)
          (fun _ h' => absurd h' Bool.false_ne_true) y hy
        rcases hR _ _ h' with ⟨Rr', _, h1, _, h4⟩ | ⟨_, _, hx, _⟩
        · exact ⟨Rr' _, _, h1 _, fun _ h' => absurd h' Bool.false_ne_true, by simpa only [rowT, rowSpecG] using h4⟩
        · exact nomatch hx
      | legacy _ =>
        simp only [rowT, rowSpecG] at hy
        refine rightC_noneP dR (P := R (.node _ a)) (fun y' h' => ?_) (hr _)
          (fun _ h' => absurd h' Bool.false_ne_true) y hy
        rcases hR _ _ h' with ⟨Rr', _, h1, _, h4⟩ | ⟨_, _, hx, _⟩
        · exact ⟨Rr' _, _, h1 _, fun _ h' => absurd h' Bool.false_ne_true, by simpa only [rowT, rowSpecG] using h4⟩
        · exact nomatch hx
      | _ => exact nomatch hk
    exact ⟨hrows, rformP dL dR hR hrows fun _ _ hx => nomatch hx⟩

variable (dL dR) in
/-- **The walk is sound** at every fuel, from the empty table: two terms that the walk separates
    share no datum. The visited relation is post-fixed, and the left answer has a derivation. -/
theorem decG_sound (laws : Laws S o) {n : Nat} {x : Graph S.sig NL} {y : Graph S.sig NR}
    (h : decG dL.sys dR.sys n [] x y = true) :
    ∀ v, (((mng τ dL x).f o v).isSome && ((mng τ dR y).f o v).isSome) = false := by
  intro v
  cases hm : (mng τ dL x).f o v with
  | none => rfl
  | some w =>
    rw [(post_soundP dL dR laws (vis_postG (sL := dL.sys) (sR := dR.sys)) (eval_of_mng dL x o v) rfl w hm).2 y
      (vis_root dL.sys dR.sys _ h)]
    rfl

end Sound

/-- **Soundness of the decision**: where `disjoint` answers `true`, no datum is accepted by both
    meanings at the orientation. -/
theorem disjoint_sound {S : Syn} [Sem S] [Leaf S.sig] [Shapes S]
    {τ : (s : Bool) → TableAt S.sig s} {o : Orient} (laws : Laws S o) {NL NR : Nat}
    {dL : Closed S.sig NL} {dR : Closed S.sig NR} {rL : Fin NL} {rR : Fin NR}
    (h : disjoint dL rL dR rR = true) (v : Mean.V (B := S.sig)) :
    (((Closed.meaning τ dL rL).f o v).isSome && ((Closed.meaning τ dR rR).f o v).isSome) = false :=
  decG_sound (Closed.toG τ dL) (Closed.toG τ dR) laws h v


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
  have hap := decG_sound (Closed.viewToG τ o dL) (Closed.viewToG τ o dR) laws h v
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
