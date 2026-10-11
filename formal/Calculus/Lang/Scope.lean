import Calculus.Lang.Term
import Calculus.Alg.System

/-!
# The scoped term: a stratified flat term over one syntactic container

`TOp B` holds one operation per constructor of the term, with the data of the constructor. Its
positions are typed: `TOp.Pos o` is the type of the children of `o`, and `TOp.pos o` enumerates
them. `TSig B` is the term container, and it holds no table. The algebra `TStep τ` runs each
operation as `denoteAbs` reads the constructor, at the tables `τ`.

A term of a scope is an `SFlat` over the term container with constants, and a closed codec is a
`DSys`. Its meaning is the solution of the DAG of scopes at a root entry.
-/

namespace Calculus.Alg

/-! ## The keys of an object, in a computable order -/

/-- One name before another in the order of `compare`, as a decision. -/
def nameLE (a b : String) : Bool := (compare a b).isLE

/-- Two names are in order one way or the other. -/
theorem nameLE_total {a b : String} (h : nameLE a b = false) : nameLE b a = true := by
  unfold nameLE at h ⊢
  rw [@Std.OrientedCmp.eq_swap _ compare String.instTransOrd.toOrientedCmp a b] at h
  cases hc : compare b a <;> simp only [hc, Ordering.swap, Ordering.isLE] at h ⊢
  all_goals exact nomatch h

/-- Two names in order both ways are one name. -/
theorem nameLE_antisymm {a b : String} (h₁ : nameLE a b = true) (h₂ : nameLE b a = true) :
    a = b := by
  unfold nameLE at h₁ h₂
  rw [@Std.OrientedCmp.eq_swap _ compare String.instTransOrd.toOrientedCmp a b] at h₁
  cases hc : compare b a with
  | eq => exact (@Std.LawfulEqCmp.eq_of_compare _ compare String.instLawfulEqOrd b a hc).symm
  | lt => simp only [hc, Ordering.swap, Ordering.isLE] at h₁; exact nomatch h₁
  | gt => simp only [hc, Ordering.isLE] at h₂; exact nomatch h₂

/-- The order of names is transitive. -/
theorem nameLE_trans {a b c : String} (h₁ : nameLE a b = true) (h₂ : nameLE b c = true) :
    nameLE a c = true :=
  @Std.TransCmp.isLE_trans _ compare String.instTransOrd a b c h₁ h₂

/-- Insert a name before the first name that does not come before it. Structural on the list. -/
def insName (a : String) : List String → List String
  | [] => [a]
  | x :: xs => cond (nameLE a x) (a :: x :: xs) (x :: insName a xs)

/-- Two insertions commute. -/
theorem insName_comm (a b : String) : ∀ l : List String, insName a (insName b l) = insName b (insName a l)
  | [] => by
      cases hab : nameLE a b <;> cases hba : nameLE b a <;>
        simp only [insName, hab, hba, cond_true, cond_false]
      · rw [nameLE_total hab] at hba; exact nomatch hba
      · rw [nameLE_antisymm hab hba]
  | x :: xs => by
      cases hbx : nameLE b x <;> cases hax : nameLE a x
      · simp only [insName, hbx, hax, cond_false]
        rw [insName_comm a b xs]
      · cases hba : nameLE b a
        · simp only [insName, hbx, hax, hba, cond_true, cond_false]
        · rw [nameLE_trans hba hax] at hbx; exact nomatch hbx
      · cases hab : nameLE a b
        · simp only [insName, hbx, hax, hab, cond_true, cond_false]
        · rw [nameLE_trans hab hbx] at hax; exact nomatch hax
      · cases hab : nameLE a b <;> cases hba : nameLE b a <;>
          simp only [insName, hbx, hax, hab, hba, cond_true, cond_false]
        · rw [nameLE_total hab] at hba; exact nomatch hba
        · rw [nameLE_antisymm hab hba]

/-- A name is in an insertion exactly where it is the inserted name or in the list. -/
theorem mem_insName {a k : String} : ∀ l : List String, k ∈ insName a l ↔ k = a ∨ k ∈ l
  | [] => by simp only [insName, List.mem_cons, List.not_mem_nil, or_false]
  | x :: xs => by
      cases h : nameLE a x
      · simp only [insName, h, cond_false, List.mem_cons, mem_insName xs]
        exact ⟨fun h' => h'.elim (fun e => .inr (.inl e)) (fun h'' => h''.elim .inl (.inr ∘ .inr)),
          fun h' => h'.elim (.inr ∘ .inl) (fun h'' => h''.elim .inl (.inr ∘ .inr))⟩
      · simp only [insName, h, cond_true, List.mem_cons]

/-- The insertion sort of names. -/
def sortNames (l : List String) : List String := l.foldr insName []

/-- **Sorting forgets the order of the list**: a permutation sorts to one list. -/
theorem sortNames_perm {l₁ l₂ : List String} (h : l₁.Perm l₂) : sortNames l₁ = sortNames l₂ := by
  induction h with
  | nil => rfl
  | cons x _ ih => exact congrArg (insName x) ih
  | swap x y l => exact insName_comm y x _
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The sorted names are the names of the list. -/
theorem mem_sortNames {k : String} : ∀ l : List String, k ∈ sortNames l ↔ k ∈ l
  | [] => Iff.rfl
  | x :: xs => by
      show k ∈ insName x (sortNames xs) ↔ _
      rw [mem_insName, mem_sortNames xs, List.mem_cons]

/-- The declared names, sorted. The insertion sort is structural, and sorting forgets the order
    of the underlying list, so the sort lifts through the quotient. -/
def keysOf (fs : Finset String) : List String :=
  Quot.liftOn fs.val sortNames fun _ _ h => sortNames_perm h

/-- The sorted names are the declared names. -/
theorem mem_keysOf {fs : Finset String} {k : String} : k ∈ keysOf fs ↔ k ∈ fs := by
  obtain ⟨v, hv⟩ := fs
  induction v using Quot.ind with
  | mk l => exact mem_sortNames l



namespace Scoped

/-- The declared names, as the members of the key set, in the order of `keysOf`. -/
def keyPos (fs : Finset String) : List {x // x ∈ fs} :=
  (keysOf fs).pmap Subtype.mk fun _ h => mem_keysOf.mp h

/-- The enumeration of the key set holds every member. -/
theorem keyPos_complete (fs : Finset String) (x : {x // x ∈ fs}) : x ∈ keyPos fs := by
  simp only [keyPos, List.mem_pmap]
  exact ⟨x.1, mem_keysOf.mpr x.2, rfl⟩

/-! ## The container -/

/-- The presence of a slot, and the constant of a `fill`. -/
inductive SlotMode (B : Sig) where
  | req
  | opt
  | fill (v : B.K)

/-- **The operations of the term**: one per constructor, with the constructor's data. -/
inductive TOp (B : Sig) where
  | prim (g : B.Ground)
  | opaq
  | never
  | set
  | list (a : Nat) (s : Fin 2) (b : Nat)
  | refine (p : B.P false) (pA : B.P true)
  | held (s : Bool) (k₀ : B.G s × Bool) (ks : List (B.G s × Bool))
  | legacy (r : B.R)
  | obj (fs : Finset String) (md : {x // x ∈ fs} → SlotMode B) (s : Fin 2)
  | union (m : Nat)

/-- **The positions of each operation.** `held` reads `true` as the inner term and `false` as the
    outer. -/
def TOp.Pos {B : Sig} : TOp B → Type
  | .prim _ | .opaq | .never => Empty
  | .set | .refine _ _ | .legacy _ => Unit
  | .held _ _ _ => Bool
  | .list a s b => Fin a ⊕ Fin s ⊕ Fin b
  | .union m => Fin m
  | .obj fs _ s => {x // x ∈ fs} ⊕ Fin s

/-- The positions of each operation, enumerated by a structural list. -/
def TOp.pos {B : Sig} : (o : TOp B) → List o.Pos
  | .prim _ | .opaq | .never => []
  | .set | .refine _ _ | .legacy _ => [()]
  | .held _ _ _ => [true, false]
  | .list a s b => (List.finRange a).map Sum.inl ++
      ((List.finRange s).map (Sum.inr ∘ Sum.inl) ++ (List.finRange b).map (Sum.inr ∘ Sum.inr))
  | .union m => List.finRange m
  | .obj fs _ s => (keyPos fs).map Sum.inl ++ (List.finRange s).map Sum.inr

/-- The enumeration of the positions of an operation holds every position. -/
theorem TOp.pos_complete {B : Sig} : ∀ (o : TOp B) (p : o.Pos), p ∈ o.pos
  | .prim _, p | .opaq, p | .never, p => nomatch p
  | .set, () | .refine _ _, () | .legacy _, () => List.mem_singleton_self ()
  | .held _ _ _, true => List.mem_cons_self
  | .held _ _ _, false => List.mem_cons_of_mem _ (List.mem_singleton_self false)
  | .list _ _ _, .inl p => List.mem_append_left _ (List.mem_map_of_mem (List.mem_finRange p))
  | .list _ _ _, .inr (.inl p) => List.mem_append_right _
      (List.mem_append_left _ (List.mem_map_of_mem (f := Sum.inr ∘ Sum.inl) (List.mem_finRange p)))
  | .list _ _ _, .inr (.inr p) => List.mem_append_right _
      (List.mem_append_right _ (List.mem_map_of_mem (f := Sum.inr ∘ Sum.inr) (List.mem_finRange p)))
  | .union _, p => List.mem_finRange p
  | .obj fs _ _, .inl x => List.mem_append_left _ (List.mem_map_of_mem (keyPos_complete fs x))
  | .obj _ _ _, .inr p => List.mem_append_right _ (List.mem_map_of_mem (List.mem_finRange p))

/-- The kind of each operation: a container is `down`, a wall is `held` or `legacy`. -/
def TOp.kind {B : Sig} : TOp B → Kind
  | .set | .list _ _ _ | .obj _ _ _ => .down
  | .held _ _ _ | .legacy _ => .wall
  | .prim _ | .opaq | .never | .refine _ _ | .union _ => .keep

/-- **The term container**: the operations of the term, their typed positions, and their kinds. It
    holds no table. -/
def TSig (B : Sig) : Container where
  A := TOp B
  B := TOp.Pos
  pos := TOp.pos
  pos_complete := TOp.pos_complete
  kind := TOp.kind

/-! ## The step -/

section Step
variable {B : Sig} [Mean B] (τ : (s : Bool) → TableAt B s)

/-- Zero or one value, from a count of `0` or `1`. -/
def optOf {X : Type} : (s : Fin 2) → (Fin s → X) → Option X
  | ⟨0, _⟩, _ => none
  | ⟨1, _⟩, f => some (f ⟨0, Nat.one_pos⟩)

/-- A slot's field from its presence and its codec. -/
def mkField : SlotMode B → Mean.C B → FieldSem (Mean.V (B := B)) (Mean.Mem (B := B))
  | .req, c => .req c
  | .opt, c => .opt c
  | .fill v, c => .fill c (Mean.const v)

/-- The open block's policy from a count and its codec. -/
def restOf : (s : Fin 2) → (Fin s → Mean.C B) → RestSem (Mean.V (B := B)) (Mean.Mem (B := B))
  | ⟨0, _⟩, _ => .refuse
  | ⟨1, _⟩, f => .codec (f ⟨0, Nat.one_pos⟩)

/-- **The codec of each operation**, the clause of `denoteAbs` for the constructor. -/
def TOp.run : (o : TOp B) → (o.Pos → Mean.C B) → Mean.C B
  | .prim g, _ => Mean.ground g
  | .opaq, _ => idCodec
  | .never, _ => .empty
  | .set, a => match Mean.set (B := B) with
    | some L => L.lift (a ())
    | none => .empty
  | .list _ s _, a => match Mean.list (B := B) with
    | some L => listCodec L.toSummand (List.ofFn fun p => a (.inl p))
        (optOf s fun p => a (.inr (.inl p))) (List.ofFn fun p => a (.inr (.inr p)))
    | none => .empty
  | .refine p pA, a => refine2 (a ()) (Mean.eval false p) (Mean.eval true pA)
  | .held s k₀ ks, a => held1 s (a true) (a false) ((τ s).word (k₀ :: ks))
  | .legacy r, a => (a ()).extendRead (Mean.read r)
  | .obj fs md s, a => match Mean.map (B := B) with
    | some F => objectCodec F.toSummand ⟨fs, fun x => mkField (md x) (a (.inl x))⟩
        (restOf s fun p => a (.inr p))
    | none => .empty
  | .union _, a => altCodec (List.ofFn a) (unanimous (List.ofFn fun p => (a p).μ))

/-- **The algebra of the term layer**, over the term container. -/
def TStep : Step (TSig B) (Mean.V (B := B)) (Mean.Mem (B := B)) where
  run := TOp.run τ

/-- The algebra runs each operation by `TOp.run`. -/
theorem TStep_run : (TStep τ).run = TOp.run τ := rfl

end Step

/-! ## The laws of the algebra -/

section Laws
variable {B : Sig} [Mean B] (τ : (s : Bool) → TableAt B s)

/-- A relation at each position relates the two lists of the positions pointwise. -/
theorem forall₂_ofFn {X Y : Type} {R : X → Y → Prop} :
    ∀ {n : Nat} {f : Fin n → X} {g : Fin n → Y}, (∀ p, R (f p) (g p)) →
      List.Forall₂ R (List.ofFn f) (List.ofFn g)
  | 0, _, _, _ => by simp
  | _ + 1, _, _, h => by
      rw [List.ofFn_succ, List.ofFn_succ]
      exact .cons (h 0) (forall₂_ofFn fun p => h p.succ)

/-- A relation of two codecs relates the two fields of one slot mode. -/
theorem mkField_rel {R : Mean.C B → Mean.C B → Prop} (s : SlotMode B) {c₁ c₂ : Mean.C B}
    (h : R c₁ c₂) : FieldSem.Rel R (mkField s c₁) (mkField s c₂) := by
  cases s with
  | req => exact h
  | opt => exact h
  | fill v => exact ⟨h, rfl⟩

/-- **The algebra keeps agreement at `keep`, and adds one layer at `down`.** -/
theorem TStep_lawful : (TStep τ).Lawful (Mean.d (B := B)) where
  keep o hk d a₁ a₂ h := by
    cases o with
    | prim g => exact AgreeLe.refl _ _
    | opaq => exact AgreeLe.refl _ _
    | never => exact AgreeLe.refl _ _
    | refine p pA => exact agreeLe_refine2 (h _) _ _
    | union m =>
      show AgreeLe _ _ (TOp.run τ (.union m) a₁) (TOp.run τ (.union m) a₂)
      exact agreeLe_altCodec _ _ (forall₂_ofFn h)
    | set => exact nomatch hk
    | list _ _ _ => exact nomatch hk
    | held _ _ _ => exact nomatch hk
    | legacy _ => exact nomatch hk
    | obj _ _ _ => exact nomatch hk
  down o hk d a₁ a₂ h := by
    cases o with
    | set =>
      show AgreeLe _ _ (TOp.run τ .set a₁) (TOp.run τ .set a₂)
      simp only [TOp.run]
      cases Mean.set (B := B) with
      | none => exact AgreeLe.refl _ _
      | some L => exact L.agree (h _)
    | list n s c =>
      show AgreeLe _ _ (TOp.run τ (.list n s c) a₁) (TOp.run τ (.list n s c) a₂)
      simp only [TOp.run]
      cases Mean.list (B := B) with
      | none => exact AgreeLe.refl _ _
      | some L =>
        refine agreeLe_listCodec L.d_lt (forall₂_ofFn fun p => h _) ?_ (forall₂_ofFn fun p => h _)
        match s with
        | ⟨0, _⟩ => exact .none
        | ⟨1, _⟩ => exact .some (h _)
    | prim g => exact nomatch hk
    | opaq => exact nomatch hk
    | never => exact nomatch hk
    | refine p pA => exact nomatch hk
    | union m => exact nomatch hk
    | held _ _ _ => exact nomatch hk
    | legacy _ => exact nomatch hk
    | obj fs md w =>
      show AgreeLe _ _ (TOp.run τ (.obj fs md w) a₁) (TOp.run τ (.obj fs md w) a₂)
      simp only [TOp.run]
      cases Mean.map (B := B) with
      | none => exact AgreeLe.refl _ _
      | some F =>
        refine agreeLe_objectCodec F.d_lt (fun k => mkField_rel _ (h _)) ?_
        match w with
        | ⟨0, _⟩ => trivial
        | ⟨1, _⟩ => exact h _

/-- `held1` reads its two codecs through their maps. -/
theorem held1_f_congr {V M : Type} {s : Bool} {w : PairAt V} {c c' P P' : Codec V M}
    (hc : c.f = c'.f) (hP : P.f = P'.f) : (held1 s c P w).f = (held1 s c' P' w).f := by
  simp only [held1, refine2, adapt2, Codec.e, Codec.p, hc, hP]

/-- `Codec.extendRead` reads its codec through its map. -/
theorem extendRead_f_congr {V M : Type} {r : V → Option V} {c c' : Codec V M} (hc : c.f = c'.f) :
    (c.extendRead r).f = (c'.extendRead r).f := by
  simp only [Codec.extendRead, Codec.ofEP, Codec.e, Codec.p, hc]

/-- **The walls of the algebra read their arguments through the maps.** -/
theorem TStep_wallF : WallF (TStep τ) := by
  intro o hk a₁ a₂ h
  cases o with
  | held s k₀ ks =>
    show (TOp.run τ (.held s k₀ ks) a₁).f = (TOp.run τ (.held s k₀ ks) a₂).f
    exact held1_f_congr (h _) (h _)
  | legacy r =>
    show (TOp.run τ (.legacy r) a₁).f = (TOp.run τ (.legacy r) a₂).f
    exact extendRead_f_congr (h _)
  | prim g => exact nomatch hk
  | opaq => exact nomatch hk
  | never => exact nomatch hk
  | set => exact nomatch hk
  | list _ _ _ => exact nomatch hk
  | refine p pA => exact nomatch hk
  | obj _ _ _ => exact nomatch hk
  | union _ => exact nomatch hk

end Laws

/-! ## The carrier -/

section Carrier
variable {B : Sig}

/-- **A term of a scope**: an `SFlat` over the term container with `c` constants. Below a container
    the term names any of the `w` entries; above every guard it names the `k` entries before its
    own. -/
abbrev Term (B : Sig) (c w k : Nat) : Type :=
  SFlat (TOp B ⊕ Fin c) (cAr (TSig B) c) (cKd (TSig B) c) w k

/-- **A flat term over the term container**, with a leaf for each of `N` entries: the graph form of
    a closed codec. -/
abbrev Graph (B : Sig) (N : Nat) : Type := Flat (TSig B).Op (TSig B).Pos N

/-- **A closed codec**: a DAG of scopes over the term container. -/
abbrev Closed (B : Sig) (N : Nat) : Type := DSys (TSig B) N

/-- **The meaning of a closed codec** at a root entry, at the tables `τ`. -/
def Closed.meaning [Mean B] (τ : (s : Bool) → TableAt B s) {N : Nat} (d : Closed B N)
    (root : Fin N) : Mean.C B :=
  d.sol (TStep τ) Mean.d root

variable {c w k : Nat}

@[match_pattern] abbrev Term.prim (g : B.Ground) : Term B c w k := .node (.inl (.prim g)) Empty.elim
@[match_pattern] abbrev Term.opaq : Term B c w k := .node (.inl .opaq) Empty.elim
@[match_pattern] abbrev Term.never : Term B c w k := .node (.inl .never) Empty.elim
@[match_pattern] abbrev Term.set (e : Term B c w w) : Term B c w k := .node (.inl .set) fun _ => e
@[match_pattern] abbrev Term.refine (t : Term B c w k) (p : B.P false) (pA : B.P true) :
    Term B c w k := .node (.inl (.refine p pA)) fun _ => t
@[match_pattern] abbrev Term.legacy (t : Term B c 0 0) (r : B.R) : Term B c w k :=
  .node (.inl (.legacy r)) fun _ => t
@[match_pattern] abbrev Term.const (i : Fin c) : Term B c w k := .node (.inr i) Empty.elim
@[match_pattern] abbrev Term.ref (i : Fin k) : Term B c w k := .leaf i

/-- The rule `(held)`: the inner term and the outer term, below the wall. -/
def Term.held (s : Bool) (inner outer : Term B c 0 0) (k₀ : B.G s × Bool)
    (ks : List (B.G s × Bool)) : Term B c w k :=
  .node (.inl (.held s k₀ ks)) fun
    | true => inner
    | false => outer

/-- The rule `(union)`, from a list of options. -/
def Term.union (os : List (Term B c w k)) : Term B c w k := .node (.inl (.union os.length)) os.get

/-- The rule `(list)`, from a prefix, at most one spread, and a suffix. -/
def Term.list (pre : List (Term B c w w)) (sp : Option (Term B c w w)) (suf : List (Term B c w w)) :
    Term B c w k :=
  match sp with
  | none => .node (.inl (.list pre.length 0 suf.length)) fun
    | .inl p => pre.get p
    | .inr (.inl p) => p.elim0
    | .inr (.inr p) => suf.get p
  | some t => .node (.inl (.list pre.length 1 suf.length)) fun
    | .inl p => pre.get p
    | .inr (.inl _) => t
    | .inr (.inr p) => suf.get p

/-- The rule `(array)`. -/
def Term.array (e : Term B c w w) : Term B c w k := Term.list [] (some e) []

/-- The rules `(tuple)` and `(tuple-tail)`. -/
def Term.tuple (es : List (Term B c w w)) (tail : Option (Term B c w w)) : Term B c w k :=
  Term.list es tail []

/-- A slot: its presence and its term. -/
abbrev ObjectSlot (B : Sig) (c w : Nat) := SlotMode B × Term B c w w

@[match_pattern] abbrev ObjectSlot.req (t : Term B c w w) : ObjectSlot B c w := (.req, t)
@[match_pattern] abbrev ObjectSlot.optional (t : Term B c w w) : ObjectSlot B c w := (.opt, t)

/-- The rule `(object)`: the declared names, the slot of each, and the open block. -/
def Term.object (fs : Finset String) (f : {x // x ∈ fs} → ObjectSlot B c w) :
    Option (Term B c w w) → Term B c w k
  | none => .node (.inl (.obj fs (fun x => (f x).1) 0)) fun
    | .inl x => (f x).2
    | .inr p => p.elim0
  | some t => .node (.inl (.obj fs (fun x => (f x).1) 1)) fun
    | .inl x => (f x).2
    | .inr _ => t

end Carrier

end Scoped

end Calculus.Alg
