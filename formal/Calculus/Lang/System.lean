import Calculus.Alg.System
import Calculus.Lang.Path

/-!
# The hoist of a term into a system of recursive codecs

Each binder of a term becomes one entry, and each variable becomes a leaf at the entry of its
binder. `hsys` is the system of a closed term: the entry of each binder is the hoist of its body.
The step of the term layer has one operation for each constructor but `union`, `mu` and `var`.
The union is the join of the step. `set`, `list` and `object` are `down`. `held` and `legacy` are
walls.

Below a wall the hoist starts an empty environment, so a binder below a wall is an entry of a
later scope, and the wall names that entry as a constant. The guard of the term justifies the
empty environment: below a wall the term reads no bound variable.

The hoisted system of each guarded closed term passes `DagGuard`, so it has a form as a DAG of
scopes. The solution of that DAG gives each binder its denotation, the whole codec, and the term
over the solution is the denotation of the term. The obligations of a union below a binder carry
`PairwiseCompat` to the solution.

The keys of an object are a `Finset String`. `keysOf` sorts them by a structural insertion sort,
lifted through the quotient, so the hoist stays structural.
-/

namespace Calculus.Alg

/-- **A binder is a system of one entry**: `denoteAbs (.mu b) ρ` is entry 0 of the one-entry
    system of `b`. -/
theorem denoteAbs_mu_one {B : Sig} [Mean B] (τ : (s : Bool) → TableAt B s) (b : Term B)
    (ρ : List (Mean.C B)) :
    denoteAbs τ (.mu b) ρ = solve Mean.d (fun env (_ : Fin 1) => denoteAbs τ b (env 0 :: ρ)) 0 :=
  (solve_one _).symm

/-! ## The nested pair at a term -/

section Nested
variable {S : Syn} [Sem S] (α : Table S) (β : Table S.op)

/-- The outer body around its inner binder: a list whose spread is the inner binder. -/
def spreadF : S.C → S.C → S.C := fun _ y =>
  match Mean.list (B := S.sig) with
  | some L => listCodec L.toSummand [] (some y) []
  | none => .empty

/-- `spreadF` is contractive in both arguments: the list reads its spread one layer down. -/
theorem spreadF_contractive : Contractive2 (Mean.d (B := S.sig)) (spreadF (S := S)) := by
  intro d _ _ y₁ y₂ _ hy
  simp only [spreadF]
  cases Mean.list (B := S.sig) with
  | none => exact AgreeLe.refl _ _
  | some L => exact agreeLe_listCodec L.d_lt .nil (.some hy) .nil

/-- An inner body that reads each variable at most one layer down is contractive in both. -/
theorem inner_contractive {c : Term S} (hg : c.guarded = true) (h0 : c.use 0 ≤ 1)
    (h1 : c.use 1 ≤ 1) :
    Contractive2 (Mean.d (B := S.sig)) fun x y => denote α β c [y, x] := by
  intro d x₁ x₂ y₁ y₂ hx hy
  refine denote_agree (α := α) (β := β) c hg (d + 1) [y₁, x₁] [y₂, x₂] fun i => ?_
  match i with
  | 0 => exact UseAgree.mono (u' := 1) hy h0
  | 1 => exact UseAgree.mono (u' := 1) hx h1
  | _ + 2 => exact UseAgree.refl _ _ _

/-- **The nested pair**: `mu (list [] (some (mu c)) [])`, where `c` reads both variables, is
    entry 0 of the pair system. The hypothesis `h1` asks that `c` read the outer variable one layer
    down. -/
theorem nested_pair {c : Term S} (hg : c.guarded = true) (h0 : c.use 0 ≤ 1) (h1 : c.use 1 ≤ 1) :
    denote α β (.mu (.list [] (some (.mu c)) [])) [] =
      solve Mean.d (pairB spreadF fun x y => denote α β c [y, x]) 0 := by
  have h : denote α β (.mu (.list [] (some (.mu c)) [])) [] = muCodec Mean.d
      (fun x => spreadF x (muCodec Mean.d fun y => denote α β c [y, x])) := by
    simp only [denote, denoteAbs, denoteListAbs, denoteOptAbs, spreadF]
    congr 1
    funext x
    cases Mean.list (B := S.sig) <;> rfl
  exact h.trans ((bekic Mean.d_pos spreadF_contractive (inner_contractive α β hg h0 h1)).1).symm

/-- The guard admits a nested pair whose inner body reads the outer variable at its own depth:
    `c.use 1 = 2`. So `nested_pair` does not cover each guarded nested pair, and the hoist does. -/
example : (Term.mu (.list [] (some (.mu (.union [.var 1, .list [.var 0] none []]))) []) :
    Term S.sig).guarded = true := rfl
example : (Term.union [.var 1, .list [.var 0] none []] : Term S.sig).use 1 = 2 := rfl

end Nested

/-! ## The obligation of a union -/

section UnionObligation
variable {S : Syn} [Sem S] (α : Table S) (β : Table S.op)

/-- Each union of a term carries pairwise compatibility at the environment of its check. -/
example (opts : List (Term S)) (ρ : List S.C) :
    Obligations α β (.union opts) ρ → PairwiseCompat α β opts ρ := fun h => h.2

/-- Under a binder, the check runs at each lawful stage. -/
example (b : Term S) (ρ : List S.C) :
    Obligations α β (.mu b) ρ ↔ ∀ n, Lawful Mean.mem (muStage (fun c => denote α β b (c :: ρ)) n) →
      Obligations α β b (muStage (fun c => denote α β b (c :: ρ)) n :: ρ) := Iff.rfl

end UnionObligation

/-! ## The binder counts of a family of blocks, by structural recursion -/

section SumF

/-- The sum of `n` counts, by structural recursion on `n`. -/
def sumF : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, c => c 0 + sumF n fun p => c p.succ

/-- A family of `n` blocks of sizes `c`, as one function on the sum. -/
def appF {X : Type} : {n : Nat} → (c : Fin n → Nat) → ((p : Fin n) → Fin (c p) → X) →
    Fin (sumF n c) → X
  | 0, _, _ => Fin.elim0
  | _ + 1, c, g => Fin.append (g 0) (appF (fun p => c p.succ) fun p => g p.succ)

/-- The place of block `p`'s element `m` in the sum. -/
def injF : {n : Nat} → (c : Fin n → Nat) → (p : Fin n) → Fin (c p) → Fin (sumF n c)
  | 0, _, p, _ => p.elim0
  | _ + 1, c, p, m => Fin.cases (motive := fun p => Fin (c p) → Fin (sumF _ c))
      (fun m => Fin.castAdd _ m) (fun q m => Fin.natAdd (c 0) (injF (fun p => c p.succ) q m)) p m

/-- Block 0 sits at the start of the sum. -/
theorem injF_zero {n : Nat} (c : Fin (n + 1) → Nat) (m : Fin (c 0)) :
    injF c 0 m = Fin.castAdd _ m := rfl

/-- Block `q + 1` sits after block 0. -/
theorem injF_succ {n : Nat} (c : Fin (n + 1) → Nat) (q : Fin n) (m : Fin (c q.succ)) :
    injF c q.succ m = Fin.natAdd (c 0) (injF (fun p => c p.succ) q m) := rfl

/-- The function on the sum reads block `p` at the place of block `p`. -/
theorem appF_injF {X : Type} : ∀ {n : Nat} (c : Fin n → Nat) (g : (p : Fin n) → Fin (c p) → X)
    (p : Fin n) (m : Fin (c p)), appF c g (injF c p m) = g p m
  | 0, _, _, p, _ => p.elim0
  | _ + 1, c, g, p, m => by
      cases p using Fin.cases with
      | zero => rw [injF_zero]; exact Fin.append_left _ _ _
      | succ q =>
        rw [injF_succ]
        exact (Fin.append_right _ _ _).trans (appF_injF (fun p => c p.succ) (fun p => g p.succ) q m)

/-- Each place in the sum is the place of an element of a block. -/
theorem sumF_cases : ∀ {n : Nat} (c : Fin n → Nat) {P : Fin (sumF n c) → Prop},
    (∀ p m, P (injF c p m)) → ∀ m, P m
  | 0, _, _, _, m => m.elim0
  | _ + 1, c, P, h, m => by
      refine Fin.addCases (fun m => ?_) (fun m => ?_) m
      · have := h 0 m
        rwa [injF_zero] at this
      · exact sumF_cases (fun p => c p.succ) (P := fun m => P (Fin.natAdd _ m))
          (fun q m => by have := h q.succ m; rwa [injF_succ] at this) m

/-- Each block is at most the sum. -/
theorem le_sumF : ∀ {n : Nat} (c : Fin n → Nat) (p : Fin n), c p ≤ sumF n c
  | 0, _, p => p.elim0
  | _ + 1, c, p => by
      cases p using Fin.cases with
      | zero => simp only [sumF]; omega
      | succ q => have := le_sumF (fun p => c p.succ) q; simp only [sumF]; omega

end SumF

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

/-- The name at a position. -/
def kAt (fs : Finset String) (p : Fin (keysOf fs).length) : {k // k ∈ fs} :=
  ⟨(keysOf fs)[p], mem_keysOf.mp (List.getElem_mem _)⟩

/-- The position of a name. -/
def idx (fs : Finset String) (k : {k // k ∈ fs}) : Fin (keysOf fs).length :=
  posOf k.1 (keysOf fs) (mem_keysOf.mpr k.2)

/-- The name at the position of a name is that name. -/
theorem kAt_idx (fs : Finset String) (k : {k // k ∈ fs}) : kAt fs (idx fs k) = k :=
  Subtype.ext (getElem_posOf _ _ _)

/-! ## The step of the term layer, and the hoist -/

section THoist
variable {S : Syn} [Sem S]

/-- The presence of a slot, and the constant of a `fill`. -/
inductive SlotKind (S : Syn) where
  | req
  | opt
  | fill (v : S.sig.K)

/-- A slot's field from its presence and its codec. -/
def mkField : SlotKind S → S.C → FieldSem (Mean.V (B := S.sig)) (Mean.Mem (B := S.sig))
  | .req, c => .req c
  | .opt, c => .opt c
  | .fill v, c => .fill c (Mean.const v)

/-- The open block's policy from its codec, where there is one. -/
def restOf : Option S.C → RestSem (Mean.V (B := S.sig)) (Mean.Mem (B := S.sig))
  | some c => .codec c
  | none => .refuse

/-- The constructors of the term, other than the union, as one step. -/
inductive TOp (S : Syn) [Sem S] where
  | prim (g : S.Ground)
  | opaq
  | never
  | set
  | list (a s c : Nat)
  | refine (p : S.sig.P false) (pA : S.sig.P true)
  | held (s : Bool) (w : PairAt (Mean.V (B := S.sig)))
  | legacy (r : S.sig.R)
  | obj (fs : Finset String) (kd : Fin (keysOf fs).length → SlotKind S) (wl : Nat)

/-- The number of arguments of each operation. -/
def TOp.arity : TOp S → Nat
  | .obj fs _ wl => (keysOf fs).length + wl
  | .list a s c => a + (s + c)
  | .set => 1
  | .refine _ _ => 1
  | .legacy _ => 1
  | .held _ _ => 2
  | .prim _ => 0
  | .opaq => 0
  | .never => 0

/-- The kind of each operation: a container is `down`, `held` and `legacy` are walls. -/
def TOp.kind : TOp S → Kind
  | .obj _ _ _ => .down
  | .set => .down
  | .list _ _ _ => .down
  | .held _ _ => .wall
  | .legacy _ => .wall
  | .prim _ => .keep
  | .opaq => .keep
  | .never => .keep
  | .refine _ _ => .keep

/-- The codec of each operation, the codec that `denote` gives the constructor. -/
def TOp.run : (o : TOp S) → (Fin o.arity → Mean.C S.sig) → Mean.C S.sig
  | .prim g, _ => Mean.ground g
  | .opaq, _ => idCodec
  | .never, _ => .empty
  | .set, a => match Mean.set (B := S.sig) with
    | some L => L.lift (a ⟨0, Nat.one_pos⟩)
    | none => .empty
  | .list n s c, a => match Mean.list (B := S.sig) with
    | some L => listCodec L.toSummand (List.ofFn fun p : Fin n => a (Fin.castAdd _ p))
        (if h : 0 < s then some (a (Fin.natAdd n (Fin.castAdd c ⟨0, h⟩))) else none)
        (List.ofFn fun p : Fin c => a (Fin.natAdd n (Fin.natAdd s p)))
    | none => .empty
  | .refine p pA, a => refine2 (a ⟨0, Nat.one_pos⟩) (Mean.eval false p) (Mean.eval true pA)
  | .held s w, a => held1 s (a ⟨0, Nat.zero_lt_two⟩) (a ⟨1, Nat.one_lt_two⟩) w
  | .legacy r, a => (a ⟨0, Nat.one_pos⟩).extendRead (Mean.read r)
  | .obj fs kd wl, a => match Mean.map (B := S.sig) with
    | some F => objectCodec F.toSummand
        ⟨fs, fun k => mkField (kd (idx fs k)) (a (Fin.castAdd wl (idx fs k)))⟩
        (restOf (if h : 0 < wl then some (a (Fin.natAdd _ ⟨0, h⟩)) else none))
    | none => .empty

/-- The base step of the term layer. -/
def TStep (S : Syn) [Sem S] : Step (Mean.V (B := S.sig)) (Mean.Mem (B := S.sig)) where
  Op := TOp S
  arity := TOp.arity
  kind := TOp.kind
  run := TOp.run

/-- A relation at each position relates the two lists of the positions pointwise. -/
theorem forall₂_ofFn {X Y : Type} {R : X → Y → Prop} :
    ∀ {n : Nat} {f : Fin n → X} {g : Fin n → Y}, (∀ p, R (f p) (g p)) →
      List.Forall₂ R (List.ofFn f) (List.ofFn g)
  | 0, _, _, _ => by simp
  | _ + 1, _, _, h => by
      rw [List.ofFn_succ, List.ofFn_succ]
      exact .cons (h 0) (forall₂_ofFn fun p => h p.succ)

/-- A relation of two codecs relates the two fields of one slot kind. -/
theorem mkField_rel {R : S.C → S.C → Prop} (s : SlotKind S) {c₁ c₂ : S.C} (h : R c₁ c₂) :
    FieldSem.Rel R (mkField s c₁) (mkField s c₂) := by
  cases s with
  | req => exact h
  | opt => exact h
  | fill v => exact ⟨h, rfl⟩

/-- The step of the term layer keeps agreement at `keep`, and adds one layer at `down`. -/
theorem TStep_lawful : (TStep S).Lawful (Mean.d (B := S.sig)) where
  keep o hk d a₁ a₂ h := by
    cases o with
    | prim g => exact AgreeLe.refl _ _
    | opaq => exact AgreeLe.refl _ _
    | never => exact AgreeLe.refl _ _
    | refine p pA => exact agreeLe_refine2 (h _) _ _
    | set => exact nomatch hk
    | list _ _ _ => exact nomatch hk
    | held _ _ => exact nomatch hk
    | legacy _ => exact nomatch hk
    | obj _ _ _ => exact nomatch hk
  down o hk d a₁ a₂ h := by
    cases o with
    | set =>
      show AgreeLe _ _ (TOp.run .set a₁) (TOp.run .set a₂)
      simp only [TOp.run]
      cases Mean.set (B := S.sig) with
      | none => exact AgreeLe.refl _ _
      | some L => exact L.agree (h _)
    | list n s c =>
      show AgreeLe _ _ (TOp.run (.list n s c) a₁) (TOp.run (.list n s c) a₂)
      simp only [TOp.run]
      cases Mean.list (B := S.sig) with
      | none => exact AgreeLe.refl _ _
      | some L =>
        refine agreeLe_listCodec L.d_lt (forall₂_ofFn fun p => h _) ?_ (forall₂_ofFn fun p => h _)
        rcases Decidable.em (0 < s) with hs | hs
        · simp only [hs, dite_true]; exact .some (h _)
        · simp only [hs, dite_false]; exact .none
    | prim g => exact nomatch hk
    | opaq => exact nomatch hk
    | never => exact nomatch hk
    | refine p pA => exact nomatch hk
    | held _ _ => exact nomatch hk
    | legacy _ => exact nomatch hk
    | obj fs kd wl =>
      show AgreeLe _ _ (TOp.run (.obj fs kd wl) a₁) (TOp.run (.obj fs kd wl) a₂)
      simp only [TOp.run]
      cases Mean.map (B := S.sig) with
      | none => exact AgreeLe.refl _ _
      | some F =>
        refine agreeLe_objectCodec F.d_lt (fun k => mkField_rel _ (h _)) ?_
        rcases Decidable.em (0 < wl) with hw | hw
        · simp only [hw, dite_true, restOf]; exact h _
        · simp only [hw, dite_false, restOf]; trivial

/-- `held1` reads its two codecs through their maps. -/
theorem held1_f_congr {V M : Type} {s : Bool} {w : PairAt V} {c c' P P' : Codec V M}
    (hc : c.f = c'.f) (hP : P.f = P'.f) : (held1 s c P w).f = (held1 s c' P' w).f := by
  simp only [held1, refine2, adapt2, Codec.e, Codec.p, hc, hP]

/-- `Codec.extendRead` reads its codec through its map. -/
theorem extendRead_f_congr {V M : Type} {r : V → Option V} {c c' : Codec V M} (hc : c.f = c'.f) :
    (c.extendRead r).f = (c'.extendRead r).f := by
  simp only [Codec.extendRead, Codec.ofEP, Codec.e, Codec.p, hc]

/-- The walls of the term layer read their arguments through the maps. -/
theorem TStep_wallF : WallF (TStep S) := by
  intro o hk a₁ a₂ h
  cases o with
  | held s w =>
    show (TOp.run (.held s w) a₁).f = (TOp.run (.held s w) a₂).f
    exact held1_f_congr (h _) (h _)
  | legacy r =>
    show (TOp.run (.legacy r) a₁).f = (TOp.run (.legacy r) a₂).f
    exact extendRead_f_congr (h _)
  | prim g => exact nomatch hk
  | opaq => exact nomatch hk
  | never => exact nomatch hk
  | set => exact nomatch hk
  | list _ _ _ => exact nomatch hk
  | refine p pA => exact nomatch hk
  | obj _ _ _ => exact nomatch hk

/-- The hoist step: the step of the term layer with the join and the restriction. -/
abbrev HS (S : Syn) [Sem S] := (TStep S).withJoin

/-- A flat term of the hoist, with `N` entries. -/
abbrev HFlat (S : Syn) [Sem S] (N : Nat) := Flat (HS S).Op (HS S).arity N

/-- The hoist step keeps the laws of a step. -/
theorem HS_lawful : (HS S).Lawful (Mean.d (B := S.sig)) := TStep_lawful.withJoin

/-- The walls of the hoist step read their arguments through the maps. -/
theorem HS_wallF : WallF (HS S)
  | .inl o, hk, a₁, a₂, h => TStep_wallF o hk a₁ a₂ h
  | .inr _, hk, _, _, _ => nomatch hk

/-! The terms that the hoist covers. `Term.frag_all` proves that the hoist covers every term. -/
mutual
def Term.frag : Term S.sig → Bool
  | .prim _ | .opaq | .never | .var _ => true
  | .set t | .refine t _ _ | .mu t | .legacy t _ => Term.frag t
  | .held _ t P _ _ => Term.frag t && Term.frag P
  | .list pre sp suf => Term.fragL pre && Term.fragO sp && Term.fragL suf
  | .union os => Term.fragL os
  | .object (.mk _ f w) => decide (∀ k, Term.fragS (f k) = true) && Term.fragO w
def Term.fragS : ObjectSlot S.sig → Bool
  | .req t | .optional t | .fill t _ => Term.frag t
def Term.fragL : List (Term S.sig) → Bool
  | [] => true
  | t :: ts => Term.frag t && Term.fragL ts
def Term.fragO : Option (Term S.sig) → Bool
  | none => true
  | some t => Term.frag t
end

omit [Sem S] in
mutual

/-- **The hoist covers every term.** -/
theorem Term.frag_all : ∀ t : Term S.sig, Term.frag t = true
  | .prim _ => rfl
  | .opaq => rfl
  | .never => rfl
  | .var _ => rfl
  | .set t => Term.frag_all t
  | .refine t _ _ => Term.frag_all t
  | .mu t => Term.frag_all t
  | .legacy t _ => Term.frag_all t
  | .held _ t P _ _ => by simp only [Term.frag, Term.frag_all t, Term.frag_all P, Bool.and_self]
  | .list pre sp suf => by
      simp only [Term.frag, Term.fragL_all pre, Term.fragO_all sp, Term.fragL_all suf, Bool.and_self]
  | .union os => Term.fragL_all os
  | .object (.mk _ f w) => by
      have h : ∀ k, Term.fragS (f k) = true := fun k => Term.fragS_all (f k)
      simp [Term.frag, h, Term.fragO_all w]

/-- The hoist covers every slot. -/
theorem Term.fragS_all : ∀ s : ObjectSlot S.sig, Term.fragS s = true
  | .req t => Term.frag_all t
  | .optional t => Term.frag_all t
  | .fill t _ => Term.frag_all t

/-- The hoist covers every list of terms. -/
theorem Term.fragL_all : ∀ ts : List (Term S.sig), Term.fragL ts = true
  | [] => rfl
  | t :: ts => by simp only [Term.fragL, Term.frag_all t, Term.fragL_all ts, Bool.and_self]

/-- The hoist covers every spread. -/
theorem Term.fragO_all : ∀ sp : Option (Term S.sig), Term.fragO sp = true
  | none => rfl
  | some t => Term.frag_all t

end

/-! The number of binders. -/
mutual
def muC : Term S.sig → Nat
  | .mu b => muC b + 1
  | .set t | .refine t _ _ | .legacy t _ => muC t
  | .held _ t P _ _ => muC t + muC P
  | .list pre sp suf => muCL pre + (muCO sp + muCL suf)
  | .union os => muCL os
  | .object (.mk fs f w) => sumF (keysOf fs).length (fun p => muCS (f (kAt fs p))) + muCO w
  | .prim _ | .opaq | .never | .var _ => 0
def muCS : ObjectSlot S.sig → Nat
  | .req t | .optional t | .fill t _ => muC t
def muCL : List (Term S.sig) → Nat
  | [] => 0
  | t :: ts => muC t + muCL ts
def muCO : Option (Term S.sig) → Nat
  | none => 0
  | some t => muC t
end

/-- The presence of a slot. -/
def slotKind : ObjectSlot S.sig → SlotKind S
  | .req _ => .req
  | .optional _ => .opt
  | .fill _ v => .fill v

/-- The number of spread positions: one where there is a spread. -/
def optLen : Option (Term S.sig) → Nat
  | none => 0
  | some _ => 1

/-- The environment under one more binder. -/
def consEnv {N : Nat} (j : Fin N) (env : Nat → Option (Fin N)) : Nat → Option (Fin N)
  | 0 => some j
  | i + 1 => env i

/-- The environment of no binder: below a wall, the hoist starts here. -/
def noEnv {N : Nat} : Nat → Option (Fin N) := fun _ => none

/-- The bottom as a flat term. -/
def neverF {N : Nat} : HFlat S N := .node (.inl .never) Fin.elim0

variable (α : Table S) (β : Table S.op)

/-! **The hoist of a term**: each binder becomes a leaf at its entry, and each variable a leaf at
    the entry of its binder. Below a wall, the environment is empty. -/
mutual
def hoist {N : Nat} : (t : Term S.sig) → (Fin (muC t) → Fin N) → (Nat → Option (Fin N)) → HFlat S N
  | .prim g, _, _ => .node (.inl (.prim g)) Fin.elim0
  | .opaq, _, _ => .node (.inl .opaq) Fin.elim0
  | .never, _, _ => neverF
  | .var i, _, env => match env i with
    | some j => .leaf j
    | none => neverF
  | .mu _, emb, _ => .leaf (emb ⟨0, Nat.succ_pos _⟩)
  | .set t, emb, env => .node (.inl .set) fun _ => hoist t emb env
  | .refine t p pA, emb, env => .node (.inl (.refine p pA)) fun _ => hoist t emb env
  | .legacy t r, emb, _ => .node (.inl (.legacy r)) fun _ => hoist t emb noEnv
  | .held s t P k₀ k, emb, _ => .node (.inl (.held s ((tables S.o α β s).word (k₀ :: k))))
      (Fin.cons (hoist t (fun m => emb (Fin.castAdd _ m)) noEnv)
        (Fin.cons (hoist P (fun m => emb (Fin.natAdd _ m)) noEnv) Fin.elim0))
  | .union os, emb, env =>
      .node (.inr (.inl (os.length, unanimous (μSynList (S := S) os)))) (hoistL os emb env)
  | .list pre sp suf, emb, env => .node (.inl (.list pre.length (optLen sp) suf.length))
      (Fin.append (hoistL pre (fun m => emb (Fin.castAdd _ m)) env)
        (Fin.append (hoistO sp (fun m => emb (Fin.natAdd _ (Fin.castAdd _ m))) env)
          (hoistL suf (fun m => emb (Fin.natAdd _ (Fin.natAdd _ m))) env)))
  | .object (.mk fs f w), emb, env =>
      .node (.inl (.obj fs (fun p => slotKind (f (kAt fs p))) (optLen w)))
        (Fin.append (fun p => hoistS (f (kAt fs p))
            (fun m => emb (Fin.castAdd _ (injF (fun p => muCS (f (kAt fs p))) p m))) env)
          (hoistO w (fun m => emb (Fin.natAdd _ m)) env))
def hoistS {N : Nat} : (s : ObjectSlot S.sig) → (Fin (muCS s) → Fin N) → (Nat → Option (Fin N)) →
    HFlat S N
  | .req t, emb, env => hoist t emb env
  | .optional t, emb, env => hoist t emb env
  | .fill t _, emb, env => hoist t emb env
def hoistL {N : Nat} : (ts : List (Term S.sig)) → (Fin (muCL ts) → Fin N) →
    (Nat → Option (Fin N)) → Fin ts.length → HFlat S N
  | [], _, _ => Fin.elim0
  | t :: ts, emb, env => Fin.cons (hoist t (fun m => emb (Fin.castAdd _ m)) env)
      (hoistL ts (fun m => emb (Fin.natAdd _ m)) env)
def hoistO {N : Nat} : (sp : Option (Term S.sig)) → (Fin (muCO sp) → Fin N) →
    (Nat → Option (Fin N)) → Fin (optLen sp) → HFlat S N
  | none, _, _ => Fin.elim0
  | some t, emb, env => fun _ => hoist t emb env
end

/-! **The system of a term**: the entry of each binder is the hoist of its body. -/
mutual
def sysOf {N : Nat} : (t : Term S.sig) → (Fin (muC t) → Fin N) → (Nat → Option (Fin N)) →
    Fin (muC t) → HFlat S N
  | .mu b, emb, env =>
      Fin.cons (hoist α β b (fun m => emb m.succ) (consEnv (emb ⟨0, Nat.succ_pos _⟩) env))
        (sysOf b (fun m => emb m.succ) (consEnv (emb ⟨0, Nat.succ_pos _⟩) env))
  | .set t, emb, env => sysOf t emb env
  | .refine t _ _, emb, env => sysOf t emb env
  | .legacy t _, emb, _ => sysOf t emb noEnv
  | .held _ t P _ _, emb, _ =>
      Fin.append (sysOf t (fun m => emb (Fin.castAdd _ m)) noEnv)
        (sysOf P (fun m => emb (Fin.natAdd _ m)) noEnv)
  | .union os, emb, env => sysOfL os emb env
  | .list pre sp suf, emb, env =>
      Fin.append (sysOfL pre (fun m => emb (Fin.castAdd _ m)) env)
        (Fin.append (sysOfO sp (fun m => emb (Fin.natAdd _ (Fin.castAdd _ m))) env)
          (sysOfL suf (fun m => emb (Fin.natAdd _ (Fin.natAdd _ m))) env))
  | .object (.mk fs f w), emb, env =>
      Fin.append (appF (fun p => muCS (f (kAt fs p))) fun p => sysOfS (f (kAt fs p))
          (fun m => emb (Fin.castAdd _ (injF (fun p => muCS (f (kAt fs p))) p m))) env)
        (sysOfO w (fun m => emb (Fin.natAdd _ m)) env)
  | .prim _, _, _ | .opaq, _, _ | .never, _, _ | .var _, _, _ => Fin.elim0
def sysOfS {N : Nat} : (s : ObjectSlot S.sig) → (Fin (muCS s) → Fin N) →
    (Nat → Option (Fin N)) → Fin (muCS s) → HFlat S N
  | .req t, emb, env => sysOf t emb env
  | .optional t, emb, env => sysOf t emb env
  | .fill t _, emb, env => sysOf t emb env
def sysOfL {N : Nat} : (ts : List (Term S.sig)) → (Fin (muCL ts) → Fin N) →
    (Nat → Option (Fin N)) → Fin (muCL ts) → HFlat S N
  | [], _, _ => Fin.elim0
  | t :: ts, emb, env => Fin.append (sysOf t (fun m => emb (Fin.castAdd _ m)) env)
      (sysOfL ts (fun m => emb (Fin.natAdd _ m)) env)
def sysOfO {N : Nat} : (sp : Option (Term S.sig)) → (Fin (muCO sp) → Fin N) →
    (Nat → Option (Fin N)) → Fin (muCO sp) → HFlat S N
  | none, _, _ => Fin.elim0
  | some t, emb, env => sysOf t emb env
end

/-! The codec of each binder: its denotation, at the environment of its position. Below a wall,
    the environment is empty. -/
mutual
def vals : (t : Term S.sig) → List S.C → Fin (muC t) → S.C
  | .mu b, ρ => Fin.cons (denote α β (.mu b) ρ) (vals b (denote α β (.mu b) ρ :: ρ))
  | .set t, ρ => vals t ρ
  | .refine t _ _, ρ => vals t ρ
  | .legacy t _, _ => vals t []
  | .held _ t P _ _, _ => Fin.append (vals t []) (vals P [])
  | .union os, ρ => valsL os ρ
  | .list pre sp suf, ρ => Fin.append (valsL pre ρ) (Fin.append (valsO sp ρ) (valsL suf ρ))
  | .object (.mk fs f w), ρ =>
      Fin.append (appF (fun p => muCS (f (kAt fs p))) fun p => valsS (f (kAt fs p)) ρ) (valsO w ρ)
  | .prim _, _ | .opaq, _ | .never, _ | .var _, _ => Fin.elim0
def valsS : (s : ObjectSlot S.sig) → List S.C → Fin (muCS s) → S.C
  | .req t, ρ => vals t ρ
  | .optional t, ρ => vals t ρ
  | .fill t _, ρ => vals t ρ
def valsL : (ts : List (Term S.sig)) → List S.C → Fin (muCL ts) → S.C
  | [], _ => Fin.elim0
  | t :: ts, ρ => Fin.append (vals t ρ) (valsL ts ρ)
def valsO : (sp : Option (Term S.sig)) → List S.C → Fin (muCO sp) → S.C
  | none, _ => Fin.elim0
  | some t, ρ => vals t ρ
end

end THoist

/-! ### A variable that a term does not read

`Term.use i t = 0` says that `t` does not read the variable `i`. Two environments that differ only
at such variables give one codec, the whole codec and not only its maps. -/

section UseCongr
variable {B : Sig} [Mean B] (τ : (s : Bool) → TableAt B s)

/-- A variable that a container body does not read, the container does not read. -/
theorem useUnder_zero {u : Nat} (h : useUnder u = 0) : u = 0 := by
  unfold useUnder at h; split at h <;> omega

/-- A wall body that reads a variable at most at level 2 does not read the variable. -/
theorem useHeld_zero {u : Nat} (h : useHeld u ≤ 2) : u = 0 := by
  unfold useHeld at h; split at h <;> omega

/-- A count below zero is zero. -/
theorem zero_of_le {a b : Nat} (h : a ≤ b) (hb : b = 0) : a = 0 := by omega

mutual

/-- **A variable that a term does not read changes nothing**: environments that differ only at
    such variables give one codec. -/
theorem denote_congr_use : ∀ (t : Term B) (ρ₁ ρ₂ : List (Mean.C B)),
    (∀ i, t.use i = 0 ∨ envAt ρ₁ i = envAt ρ₂ i) → denoteAbs τ t ρ₁ = denoteAbs τ t ρ₂
  | .prim _, _, _, _ => rfl
  | .opaq, _, _, _ => rfl
  | .never, _, _, _ => rfl
  | .var j, _, _, h => by
      rcases h j with h | h
      · simp [Term.use] at h
      · exact h
  | .set t, ρ₁, ρ₂, h => by
      simp only [denoteAbs]
      rw [denote_congr_use t ρ₁ ρ₂ fun i => (h i).imp_left fun h => useUnder_zero h]
  | .refine t _ _, ρ₁, ρ₂, h => by
      simp only [denoteAbs]
      rw [denote_congr_use t ρ₁ ρ₂ fun i => (h i).imp_left id]
  | .legacy t _, ρ₁, ρ₂, h => by
      simp only [denoteAbs]
      rw [denote_congr_use t ρ₁ ρ₂ fun i => (h i).imp_left fun h => useHeld_zero (by
        simp only [Term.use] at h; omega)]
  | .held _ t P _ _, ρ₁, ρ₂, h => by
      simp only [denoteAbs]
      have h0 : ∀ i, max (t.use i) (P.use i) = 0 ∨ envAt ρ₁ i = envAt ρ₂ i := fun i =>
        (h i).imp_left fun h => useHeld_zero (by simp only [Term.use] at h; omega)
      rw [denote_congr_use t ρ₁ ρ₂ fun i => (h0 i).imp_left fun h => zero_of_le (le_max_left _ _) h,
        denote_congr_use P ρ₁ ρ₂ fun i => (h0 i).imp_left fun h => zero_of_le (le_max_right _ _) h]
  | .mu b, ρ₁, ρ₂, h => by
      simp only [denoteAbs]
      congr 1
      funext c
      exact denote_congr_use b (c :: ρ₁) (c :: ρ₂) fun i => match i with
        | 0 => .inr rfl
        | i + 1 => (h i).imp_left fun h => by simpa [Term.use] using h
  | .list pre sp suf, ρ₁, ρ₂, h => by
      simp only [denoteAbs]
      have h0 : ∀ i, max (Term.useL i pre) (max (Term.useO i sp) (Term.useL i suf)) = 0 ∨
          envAt ρ₁ i = envAt ρ₂ i := fun i =>
        (h i).imp_left fun h => useUnder_zero (by simpa [Term.use] using h)
      rw [denoteListAbs_congr_use pre ρ₁ ρ₂ fun i => (h0 i).imp_left fun h =>
          zero_of_le (le_max_left _ _) h,
        denoteOptAbs_congr_use sp ρ₁ ρ₂ fun i => (h0 i).imp_left fun h =>
          zero_of_le (le_trans (le_max_left _ _) (le_max_right _ _)) h,
        denoteListAbs_congr_use suf ρ₁ ρ₂ fun i => (h0 i).imp_left fun h =>
          zero_of_le (le_trans (le_max_right _ _) (le_max_right _ _)) h]
  | .object b, ρ₁, ρ₂, h => bodySemAbs_congr_use b ρ₁ ρ₂ fun i =>
      (h i).imp_left fun h => useUnder_zero (by simpa [Term.use] using h)
  | .union os, ρ₁, ρ₂, h => by
      simp only [denoteAbs]
      have h0 : ∀ i, Term.useL i os = 0 ∨ envAt ρ₁ i = envAt ρ₂ i := fun i =>
        (h i).imp_left fun h => by simpa [Term.use] using h
      rw [denoteListAbs_congr_use os ρ₁ ρ₂ h0, denoteμsAbs_congr_use os ρ₁ ρ₂ h0]

/-- The body form of `denote_congr_use`. -/
theorem bodySemAbs_congr_use : ∀ (b : Body B) (ρ₁ ρ₂ : List (Mean.C B)),
    (∀ i, b.use i = 0 ∨ envAt ρ₁ i = envAt ρ₂ i) → bodySemAbs τ b ρ₁ = bodySemAbs τ b ρ₂
  | .mk fields f wild, ρ₁, ρ₂, h => by
      have hf : (fun k => fieldSemAbs τ (f k) ρ₁) = (fun k => fieldSemAbs τ (f k) ρ₂) :=
        funext fun k => fieldSemAbs_congr_use (f k) ρ₁ ρ₂ fun i => (h i).imp_left fun h =>
          zero_of_le (le_trans (Finset.le_sup (f := fun k => ObjectSlot.use i (f k))
            (Finset.mem_attach _ k)) (le_max_left _ _)) h
      simp only [bodySemAbs]
      rw [hf, wildSemAbs_congr_use wild ρ₁ ρ₂ fun i => (h i).imp_left fun h =>
        zero_of_le (le_max_right _ _) h]

/-- The slot form of `denote_congr_use`. -/
theorem fieldSemAbs_congr_use : ∀ (s : ObjectSlot B) (ρ₁ ρ₂ : List (Mean.C B)),
    (∀ i, s.use i = 0 ∨ envAt ρ₁ i = envAt ρ₂ i) → fieldSemAbs τ s ρ₁ = fieldSemAbs τ s ρ₂
  | .req t, ρ₁, ρ₂, h => by
      simp only [fieldSemAbs]; rw [denote_congr_use t ρ₁ ρ₂ h]
  | .optional t, ρ₁, ρ₂, h => by
      simp only [fieldSemAbs]; rw [denote_congr_use t ρ₁ ρ₂ h]
  | .fill t _, ρ₁, ρ₂, h => by
      simp only [fieldSemAbs]; rw [denote_congr_use t ρ₁ ρ₂ h]

/-- The open block form of `denote_congr_use`. -/
theorem wildSemAbs_congr_use : ∀ (w : Option (Term B)) (ρ₁ ρ₂ : List (Mean.C B)),
    (∀ i, Term.useO i w = 0 ∨ envAt ρ₁ i = envAt ρ₂ i) → wildSemAbs τ w ρ₁ = wildSemAbs τ w ρ₂
  | none, _, _, _ => rfl
  | some t, ρ₁, ρ₂, h => by
      simp only [wildSemAbs]; rw [denote_congr_use t ρ₁ ρ₂ h]

/-- The list form of `denote_congr_use`. -/
theorem denoteListAbs_congr_use : ∀ (ts : List (Term B)) (ρ₁ ρ₂ : List (Mean.C B)),
    (∀ i, Term.useL i ts = 0 ∨ envAt ρ₁ i = envAt ρ₂ i) →
    denoteListAbs τ ts ρ₁ = denoteListAbs τ ts ρ₂
  | [], _, _, _ => rfl
  | t :: ts, ρ₁, ρ₂, h => by
      simp only [denoteListAbs]
      rw [denote_congr_use t ρ₁ ρ₂ fun i => (h i).imp_left fun h =>
          zero_of_le (le_max_left _ _) h,
        denoteListAbs_congr_use ts ρ₁ ρ₂ fun i => (h i).imp_left fun h =>
          zero_of_le (le_max_right _ _) h]

/-- The spread form of `denote_congr_use`. -/
theorem denoteOptAbs_congr_use : ∀ (sp : Option (Term B)) (ρ₁ ρ₂ : List (Mean.C B)),
    (∀ i, Term.useO i sp = 0 ∨ envAt ρ₁ i = envAt ρ₂ i) →
    denoteOptAbs τ sp ρ₁ = denoteOptAbs τ sp ρ₂
  | none, _, _, _ => rfl
  | some t, ρ₁, ρ₂, h => by
      simp only [denoteOptAbs]; rw [denote_congr_use t ρ₁ ρ₂ h]

/-- The form of `denote_congr_use` for the members of a union. -/
theorem denoteμsAbs_congr_use : ∀ (ts : List (Term B)) (ρ₁ ρ₂ : List (Mean.C B)),
    (∀ i, Term.useL i ts = 0 ∨ envAt ρ₁ i = envAt ρ₂ i) →
    denoteμsAbs τ ts ρ₁ = denoteμsAbs τ ts ρ₂
  | [], _, _, _ => rfl
  | t :: ts, ρ₁, ρ₂, h => by
      simp only [denoteμsAbs]
      rw [denote_congr_use t ρ₁ ρ₂ fun i => (h i).imp_left fun h =>
          zero_of_le (le_max_left _ _) h,
        denoteμsAbs_congr_use ts ρ₁ ρ₂ fun i => (h i).imp_left fun h =>
          zero_of_le (le_max_right _ _) h]

end

end UseCongr


/-! ### The hoist means what the term means -/

section THoistLaws
variable {S : Syn} [Sem S] (α : Table S) (β : Table S.op)

/-- The codec that an environment of entries gives a variable. -/
def envOf {N : Nat} (e : Fin N → S.C) (env : Nat → Option (Fin N)) (i : Nat) : S.C :=
  match env i with
  | some j => e j
  | none => .empty

/-- A variable past the environment reads the empty codec. -/
theorem envAt_ge {V M : Type} : ∀ (ρ : List (Codec V M)) (i : Nat), ρ.length ≤ i →
    envAt ρ i = .empty
  | [], _, _ => rfl
  | _ :: ρ, i + 1, h => envAt_ge ρ i (Nat.le_of_succ_le_succ h)
  | _ :: _, 0, h => absurd h (Nat.not_succ_le_zero _)

/-- Where no variable carries a member, the members of the options are the syntactic members. -/
theorem denoteμs_syn {ρ : List S.C} (hμ : ∀ i, (envAt ρ i).μ = none) :
    ∀ os : List (Term S.sig), denoteμs α β os ρ = μSynList (S := S) os
  | [] => rfl
  | t :: ts => by
      show (denote α β t ρ).μ :: denoteμs α β ts ρ = μSyn (S := S) t :: μSynList (S := S) ts
      rw [denote_μ_eq t ρ hμ, denoteμs_syn hμ ts]

/-- A container body that the guard admits reads each variable at most at level 2. -/
theorem useUnder_le {u : Nat} (h : useUnder u ≤ 2) : u ≤ 2 := by
  unfold useUnder at h; split at h <;> omega

/-- **Below a wall, the term reads no bound variable**, so the empty environment gives its codec. -/
theorem denote_wall {t : Term S.sig} {ρ : List S.C} (h : ∀ i, i < ρ.length → t.use i = 0) :
    denote α β t [] = denote α β t ρ :=
  denote_congr_use _ t [] ρ fun i => by
    rcases Nat.lt_or_ge i ρ.length with hi | hi
    · exact .inl (h i hi)
    · exact .inr (envAt_ge ρ i hi).symm

omit [Sem S] in
/-- A slot reads a variable at most as the object reads it. -/
theorem slot_use_le {fs : Finset String} {f : {k // k ∈ fs} → ObjectSlot S.sig}
    {w : Option (Term S.sig)} (i : Nat) (k : {k // k ∈ fs}) :
    ObjectSlot.use i (f k) ≤ Body.use i (.mk fs f w) := by
  simp only [Body.use]
  exact le_trans (Finset.le_sup (f := fun k => ObjectSlot.use i (f k)) (Finset.mem_attach _ k))
    (le_max_left _ _)

omit [Sem S] in
/-- The open block reads a variable at most as the object reads it. -/
theorem wild_use_le {fs : Finset String} {f : {k // k ∈ fs} → ObjectSlot S.sig}
    {w : Option (Term S.sig)} (i : Nat) : Term.useO i w ≤ Body.use i (.mk fs f w) := by
  simp only [Body.use]; exact le_max_right _ _

/-- The policy of the open block is the policy of its denotation. -/
theorem restOf_denoteOpt (w : Option (Term S.sig)) (ρ : List S.C) :
    restOf (denoteOpt α β w ρ) = wildSemAbs (tables S.o α β) w ρ := by
  cases w <;> rfl

mutual

/-- **The hoist's codec is the denotation**, where each entry holds its binder's codec. -/
theorem interp_hoist {N : Nat} (e : Fin N → S.C) : ∀ (t : Term S.sig), Term.frag t = true →
    t.guarded = true → ∀ (ρ : List S.C) (emb : Fin (muC t) → Fin N) (env : Nat → Option (Fin N)),
    (∀ i, i < ρ.length → t.use i ≤ 2) →
    (∀ i, envAt ρ i = envOf e env i) → (∀ i, (envAt ρ i).μ = none) →
    (∀ m, e (emb m) = vals α β t ρ m) → (hoist α β t emb env).interp (HS S) e = denote α β t ρ
  | .prim _, _, _, _, _, _, _, _, _, _ => rfl
  | .opaq, _, _, _, _, _, _, _, _, _ => rfl
  | .never, _, _, _, _, _, _, _, _, _ => rfl
  | .var i, _, _, ρ, _, env, _, hρ, _, _ => by
      show _ = envAt ρ i
      rw [hρ i]
      simp only [hoist, envOf]
      cases env i <;> rfl
  | .mu _, _, _, _, _, _, _, _, _, hv => hv ⟨0, Nat.succ_pos _⟩
  | .set t, hf, hg, ρ, emb, env, hU, hρ, hμ, hv => by
      have ih := interp_hoist e t hf hg ρ emb env (fun i hi => useUnder_le (hU i hi)) hρ hμ hv
      show TOp.run .set (fun _ => (hoist α β t emb env).interp (HS S) e) = _
      rw [ih]
      simp only [TOp.run, denote, denoteAbs]
      cases Mean.set (B := S.sig) <;> rfl
  | .refine t p pA, hf, hg, ρ, emb, env, hU, hρ, hμ, hv => by
      have ih := interp_hoist e t hf hg ρ emb env hU hρ hμ hv
      show TOp.run (.refine p pA) (fun _ => (hoist α β t emb env).interp (HS S) e) = _
      rw [ih]
      simp only [TOp.run, denote, denoteAbs]
  | .legacy t r, hf, hg, ρ, emb, _, hU, _, _, hv => by
      have ih := interp_hoist e t hf hg [] emb noEnv (fun _ h => absurd h (Nat.not_lt_zero _))
        (fun _ => rfl) (fun _ => rfl) hv
      show TOp.run (.legacy r) (fun _ => (hoist α β t emb noEnv).interp (HS S) e) = _
      rw [ih, denote_wall α β fun i hi => useHeld_zero (hU i hi)]
      simp only [TOp.run, denote, denoteAbs]
  | .held s t P k₀ k, hf, hg, ρ, emb, _, hU, _, _, hv => by
      simp only [Term.frag, Bool.and_eq_true] at hf
      simp only [Term.guarded, Bool.and_eq_true] at hg
      have h0 : ∀ i, i < ρ.length → max (t.use i) (P.use i) = 0 := fun i hi => useHeld_zero (hU i hi)
      have iht := interp_hoist e t hf.1 hg.1 [] _ noEnv (fun _ h => absurd h (Nat.not_lt_zero _))
        (fun _ => rfl) (fun _ => rfl) fun m => by
          have := hv (Fin.castAdd _ m); simpa [vals] using this
      have ihP := interp_hoist e P hf.2 hg.2 [] _ noEnv (fun _ h => absurd h (Nat.not_lt_zero _))
        (fun _ => rfl) (fun _ => rfl) fun m => by
          have := hv (Fin.natAdd _ m); simpa [vals] using this
      show held1 s ((hoist α β t _ noEnv).interp (HS S) e) ((hoist α β P _ noEnv).interp (HS S) e) _ = _
      rw [iht, ihP, denote_wall α β fun i hi => zero_of_le (le_max_left _ _) (h0 i hi),
        denote_wall α β fun i hi => zero_of_le (le_max_right _ _) (h0 i hi)]
      rfl
  | .union os, hf, hg, ρ, emb, env, hU, hρ, hμ, hv => by
      have ih := interp_hoistL e os hf hg ρ emb env hU hρ hμ hv
      show altCodec ((List.finRange os.length).map fun p => (hoistL α β os emb env p).interp (HS S) e) _ =
        altCodec (denoteList α β os ρ) (unanimous (denoteμs α β os ρ))
      rw [← List.ofFn_eq_map, ih, denoteμs_syn α β hμ os]
  | .list pre sp suf, hf, hg, ρ, emb, env, hU, hρ, hμ, hv => by
      simp only [Term.frag, Bool.and_eq_true] at hf
      simp only [Term.guarded, Bool.and_eq_true] at hg
      have hU' : ∀ i, i < ρ.length →
          max (Term.useL i pre) (max (Term.useO i sp) (Term.useL i suf)) ≤ 2 :=
        fun i hi => useUnder_le (hU i hi)
      have ihp := interp_hoistL e pre hf.1.1 hg.1.1 ρ _ env
        (fun i hi => le_trans (le_max_left _ _) (hU' i hi)) hρ hμ fun m => by
          have := hv (Fin.castAdd _ m); simpa [vals] using this
      have ihs := interp_hoistO e sp hf.1.2 hg.1.2 ρ _ env
        (fun i hi => le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (hU' i hi)) hρ hμ
        fun m => by have := hv (Fin.natAdd _ (Fin.castAdd _ m)); simpa [vals] using this
      have ihf := interp_hoistL e suf hf.2 hg.2 ρ _ env
        (fun i hi => le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (hU' i hi)) hρ hμ
        fun m => by have := hv (Fin.natAdd _ (Fin.natAdd _ m)); simpa [vals] using this
      show TOp.run (.list pre.length (optLen sp) suf.length) (fun p => Flat.interp (HS S) e
          (Fin.append (hoistL α β pre (fun m => emb (Fin.castAdd _ m)) env)
            (Fin.append (hoistO α β sp (fun m => emb (Fin.natAdd _ (Fin.castAdd _ m))) env)
              (hoistL α β suf (fun m => emb (Fin.natAdd _ (Fin.natAdd _ m))) env)) p)) =
        denote α β (.list pre sp suf) ρ
      simp only [TOp.run, Fin.append_left, Fin.append_right, denote, denoteAbs]
      rw [ihp, ihs, ihf]
      cases Mean.list (B := S.sig) <;> rfl
  | .object (.mk fs f w), hf, hg, ρ, emb, env, hU, hρ, hμ, hv => by
      simp only [Term.frag, Bool.and_eq_true, decide_eq_true_eq] at hf
      simp only [Term.guarded, Body.guarded, Bool.and_eq_true, decide_eq_true_eq] at hg
      have hUb : ∀ i, i < ρ.length → Body.use i (.mk fs f w) ≤ 2 := fun i hi => useUnder_le (hU i hi)
      have ihs : ∀ p, mkField (slotKind (f (kAt fs p))) ((hoistS α β (f (kAt fs p))
          (fun m => emb (Fin.castAdd _ (injF (fun p => muCS (f (kAt fs p))) p m))) env).interp (HS S) e) =
          fieldSem α β (f (kAt fs p)) ρ := fun p =>
        interp_hoistS e (f (kAt fs p)) (hf.1 _) (hg.1 _) ρ _ env
          (fun i hi => le_trans (slot_use_le i _) (hUb i hi)) hρ hμ fun m => by
            have := hv (Fin.castAdd _ (injF _ p m)); simpa [vals, appF_injF] using this
      have ihs2 : ∀ k, mkField (slotKind (f (kAt fs (idx fs k)))) ((hoistS α β (f (kAt fs (idx fs k)))
          (fun m => emb (Fin.castAdd _ (injF (fun p => muCS (f (kAt fs p))) (idx fs k) m))) env).interp
            (HS S) e) = fieldSemAbs (tables S.o α β) (f k) ρ := fun k =>
        (ihs (idx fs k)).trans (congrArg (fun x => fieldSem α β (f x) ρ) (kAt_idx fs k))
      have ihw := interp_hoistO e w hf.2 hg.2 ρ _ env
        (fun i hi => le_trans (wild_use_le i) (hUb i hi)) hρ hμ fun m => by
          have := hv (Fin.natAdd _ m); simpa [vals] using this
      show TOp.run (.obj fs (fun p => slotKind (f (kAt fs p))) (optLen w)) (fun q => Flat.interp (HS S) e
          (Fin.append (fun p => hoistS α β (f (kAt fs p))
              (fun m => emb (Fin.castAdd _ (injF (fun p => muCS (f (kAt fs p))) p m))) env)
            (hoistO α β w (fun m => emb (Fin.natAdd _ m)) env) q)) = denote α β (.object (.mk fs f w)) ρ
      simp only [TOp.run, Fin.append_left, Fin.append_right, denote, denoteAbs, bodySemAbs]
      rw [ihw, restOf_denoteOpt]
      simp only [ihs2]
      cases Mean.map (B := S.sig) <;> rfl

/-- The slot form of `interp_hoist`. -/
theorem interp_hoistS {N : Nat} (e : Fin N → S.C) : ∀ (s : ObjectSlot S.sig), Term.fragS s = true →
    s.guarded = true → ∀ (ρ : List S.C) (emb : Fin (muCS s) → Fin N) (env : Nat → Option (Fin N)),
    (∀ i, i < ρ.length → s.use i ≤ 2) →
    (∀ i, envAt ρ i = envOf e env i) → (∀ i, (envAt ρ i).μ = none) →
    (∀ m, e (emb m) = valsS α β s ρ m) →
    mkField (slotKind s) ((hoistS α β s emb env).interp (HS S) e) = fieldSem α β s ρ
  | .req t, hf, hg, ρ, emb, env, hU, hρ, hμ, hv => by
      show FieldSem.req ((hoist α β t emb env).interp (HS S) e) = FieldSem.req _
      rw [interp_hoist e t hf hg ρ emb env hU hρ hμ hv]
  | .optional t, hf, hg, ρ, emb, env, hU, hρ, hμ, hv => by
      show FieldSem.opt ((hoist α β t emb env).interp (HS S) e) = FieldSem.opt _
      rw [interp_hoist e t hf hg ρ emb env hU hρ hμ hv]
  | .fill t _, hf, hg, ρ, emb, env, hU, hρ, hμ, hv => by
      show FieldSem.fill ((hoist α β t emb env).interp (HS S) e) _ = FieldSem.fill _ _
      rw [interp_hoist e t hf hg ρ emb env hU hρ hμ hv]

/-- The list form of `interp_hoist`. -/
theorem interp_hoistL {N : Nat} (e : Fin N → S.C) : ∀ (ts : List (Term S.sig)),
    Term.fragL ts = true → Term.guardedL ts = true →
    ∀ (ρ : List S.C) (emb : Fin (muCL ts) → Fin N) (env : Nat → Option (Fin N)),
    (∀ i, i < ρ.length → Term.useL i ts ≤ 2) →
    (∀ i, envAt ρ i = envOf e env i) → (∀ i, (envAt ρ i).μ = none) →
    (∀ m, e (emb m) = valsL α β ts ρ m) →
    (List.ofFn fun p => (hoistL α β ts emb env p).interp (HS S) e) = denoteList α β ts ρ
  | [], _, _, _, _, _, _, _, _, _ => rfl
  | t :: ts, hf, hg, ρ, emb, env, hU, hρ, hμ, hv => by
      simp only [Term.fragL, Bool.and_eq_true] at hf
      simp only [Term.guardedL, Bool.and_eq_true] at hg
      rw [List.ofFn_succ]
      simp only [hoistL, Fin.cons_zero, Fin.cons_succ]
      rw [interp_hoist e t hf.1 hg.1 ρ _ env (fun i hi => le_trans (le_max_left _ _) (hU i hi))
          hρ hμ (fun m => by have := hv (Fin.castAdd _ m); simpa [valsL] using this),
        interp_hoistL e ts hf.2 hg.2 ρ _ env (fun i hi => le_trans (le_max_right _ _) (hU i hi))
          hρ hμ (fun m => by have := hv (Fin.natAdd _ m); simpa [valsL] using this)]
      rfl

/-- The spread form of `interp_hoist`. -/
theorem interp_hoistO {N : Nat} (e : Fin N → S.C) : ∀ (sp : Option (Term S.sig)),
    Term.fragO sp = true → Term.guardedO sp = true →
    ∀ (ρ : List S.C) (emb : Fin (muCO sp) → Fin N) (env : Nat → Option (Fin N)),
    (∀ i, i < ρ.length → Term.useO i sp ≤ 2) →
    (∀ i, envAt ρ i = envOf e env i) → (∀ i, (envAt ρ i).μ = none) →
    (∀ m, e (emb m) = valsO α β sp ρ m) →
    (if h : 0 < optLen sp then some ((hoistO α β sp emb env ⟨0, h⟩).interp (HS S) e) else none) =
      denoteOpt α β sp ρ
  | none, _, _, _, _, _, _, _, _, _ => rfl
  | some t, hf, hg, ρ, emb, env, hU, hρ, hμ, hv => by
      show some ((hoist α β t emb env).interp (HS S) e) = some (denote α β t ρ)
      rw [interp_hoist e t hf hg ρ emb env hU hρ hμ hv]

end

/-- The environment of a binder's body: the binder's codec, then the environment. -/
theorem env_mu {N : Nat} {e : Fin N → S.C} {b : Term S.sig} {ρ : List S.C}
    {emb : Fin (muC (Term.mu b)) → Fin N} {env : Nat → Option (Fin N)}
    (hρ : ∀ i, envAt ρ i = envOf e env i) (hX : e (emb ⟨0, Nat.succ_pos _⟩) = denote α β (.mu b) ρ) :
    ∀ i, envAt (denote α β (.mu b) ρ :: ρ) i = envOf e (consEnv (emb ⟨0, Nat.succ_pos _⟩) env) i
  | 0 => hX.symm
  | i + 1 => hρ i

mutual

/-- **The binders' codecs are a fixed point of the hoisted system.** -/
theorem fix_sysOf {N : Nat} (e : Fin N → S.C) : ∀ (t : Term S.sig), Term.frag t = true →
    t.guarded = true →
    ∀ (ρ : List S.C) (emb : Fin (muC t) → Fin N) (env : Nat → Option (Fin N)),
    (∀ i, i < ρ.length → t.use i ≤ 2) →
    (∀ i, envAt ρ i = envOf e env i) → (∀ i, (envAt ρ i).μ = none) →
    (∀ m, e (emb m) = vals α β t ρ m) →
    ∀ m, (e (emb m)).f = ((sysOf α β t emb env m).interp (HS S) e).f
  | .mu b, hf, hg, ρ, emb, env, hU, hρ, hμ, hv, m => by
      have hg' := hg
      simp only [Term.guarded, Bool.and_eq_true, decide_eq_true_eq] at hg'
      have hX : e (emb ⟨0, Nat.succ_pos _⟩) = denote α β (.mu b) ρ := hv _
      have hρ' := env_mu α β hρ hX
      have hμ' : ∀ i, (envAt (denote α β (.mu b) ρ :: ρ) i).μ = none := fun i => match i with
        | 0 => rfl
        | i + 1 => hμ i
      have hU' : ∀ i, i < (denote α β (.mu b) ρ :: ρ).length → b.use i ≤ 2 := fun i hi =>
        match i with
        | 0 => le_trans hg'.1 (by omega)
        | i + 1 => hU i (Nat.lt_of_succ_lt_succ hi)
      have hv' : ∀ m, e (emb m.succ) = vals α β b (denote α β (.mu b) ρ :: ρ) m := fun m =>
        (hv m.succ).trans (Fin.cons_succ _ _ _)
      change Fin (muC b + 1) at m
      cases m using Fin.cases with
      | zero =>
        show (e (emb ⟨0, Nat.succ_pos _⟩)).f = ((hoist α β b _ _).interp (HS S) e).f
        rw [interp_hoist α β e b hf hg'.2 _ _ _ hU' hρ' hμ' hv', hX]
        funext o x
        exact muCodec_fix Mean.d_pos (contractive_body hg ρ) o x
      | succ m => exact fix_sysOf e b hf hg'.2 _ _ _ hU' hρ' hμ' hv' m
  | .set t, hf, hg, ρ, emb, env, hU, hρ, hμ, hv, m =>
      fix_sysOf e t hf hg ρ emb env (fun i hi => useUnder_le (hU i hi)) hρ hμ hv m
  | .refine t _ _, hf, hg, ρ, emb, env, hU, hρ, hμ, hv, m => fix_sysOf e t hf hg ρ emb env hU hρ hμ hv m
  | .legacy t _, hf, hg, _, emb, _, _, _, _, hv, m =>
      fix_sysOf e t hf hg [] emb noEnv (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ => rfl)
        (fun _ => rfl) hv m
  | .held _ t P _ _, hf, hg, _, emb, _, _, _, _, hv, m => by
      simp only [Term.frag, Bool.and_eq_true] at hf
      simp only [Term.guarded, Bool.and_eq_true] at hg
      refine Fin.addCases (fun m => ?_) (fun m => ?_) m
      · have := fix_sysOf e t hf.1 hg.1 [] (fun m => emb (Fin.castAdd _ m)) noEnv
          (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ => rfl) (fun _ => rfl)
          (fun m => by have := hv (Fin.castAdd _ m); simpa [vals] using this) m
        simpa [sysOf] using this
      · have := fix_sysOf e P hf.2 hg.2 [] (fun m => emb (Fin.natAdd _ m)) noEnv
          (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ => rfl) (fun _ => rfl)
          (fun m => by have := hv (Fin.natAdd _ m); simpa [vals] using this) m
        simpa [sysOf] using this
  | .union os, hf, hg, ρ, emb, env, hU, hρ, hμ, hv, m => fix_sysOfL e os hf hg ρ emb env hU hρ hμ hv m
  | .list pre sp suf, hf, hg, ρ, emb, env, hU, hρ, hμ, hv, m => by
      simp only [Term.frag, Bool.and_eq_true] at hf
      simp only [Term.guarded, Bool.and_eq_true] at hg
      have hU' : ∀ i, i < ρ.length →
          max (Term.useL i pre) (max (Term.useO i sp) (Term.useL i suf)) ≤ 2 :=
        fun i hi => useUnder_le (hU i hi)
      refine Fin.addCases (fun m => ?_) (fun m => Fin.addCases (fun m => ?_) (fun m => ?_) m) m
      · have := fix_sysOfL e pre hf.1.1 hg.1.1 ρ (fun m => emb (Fin.castAdd _ m)) env
          (fun i hi => le_trans (le_max_left _ _) (hU' i hi)) hρ hμ
          (fun m => by have := hv (Fin.castAdd _ m); simpa [vals] using this) m
        simpa [sysOf] using this
      · have := fix_sysOfO e sp hf.1.2 hg.1.2 ρ (fun m => emb (Fin.natAdd _ (Fin.castAdd _ m))) env
          (fun i hi => le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (hU' i hi)) hρ hμ
          (fun m => by have := hv (Fin.natAdd _ (Fin.castAdd _ m)); simpa [vals] using this) m
        simpa [sysOf] using this
      · have := fix_sysOfL e suf hf.2 hg.2 ρ (fun m => emb (Fin.natAdd _ (Fin.natAdd _ m))) env
          (fun i hi => le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (hU' i hi)) hρ hμ
          (fun m => by have := hv (Fin.natAdd _ (Fin.natAdd _ m)); simpa [vals] using this) m
        simpa [sysOf] using this
  | .prim _, _, _, _, _, _, _, _, _, _, m => m.elim0
  | .opaq, _, _, _, _, _, _, _, _, _, m => m.elim0
  | .never, _, _, _, _, _, _, _, _, _, m => m.elim0
  | .var _, _, _, _, _, _, _, _, _, _, m => m.elim0
  | .object (.mk fs f w), hf, hg, ρ, emb, env, hU, hρ, hμ, hv, m => by
      simp only [Term.frag, Bool.and_eq_true, decide_eq_true_eq] at hf
      simp only [Term.guarded, Body.guarded, Bool.and_eq_true, decide_eq_true_eq] at hg
      have hUb : ∀ i, i < ρ.length → Body.use i (.mk fs f w) ≤ 2 := fun i hi => useUnder_le (hU i hi)
      refine Fin.addCases (fun m => ?_) (fun m => ?_) m
      · revert m
        refine sumF_cases _ (fun p m => ?_)
        have := fix_sysOfS e (f (kAt fs p)) (hf.1 _) (hg.1 _) ρ
          (fun m => emb (Fin.castAdd _ (injF (fun p => muCS (f (kAt fs p))) p m))) env
          (fun i hi => le_trans (slot_use_le i _) (hUb i hi)) hρ hμ
          (fun m => by have := hv (Fin.castAdd _ (injF _ p m)); simpa [vals, appF_injF] using this) m
        simpa [sysOf, appF_injF] using this
      · have := fix_sysOfO e w hf.2 hg.2 ρ (fun m => emb (Fin.natAdd _ m)) env
          (fun i hi => le_trans (wild_use_le i) (hUb i hi)) hρ hμ
          (fun m => by have := hv (Fin.natAdd _ m); simpa [vals] using this) m
        simpa [sysOf] using this

/-- The slot form of `fix_sysOf`. -/
theorem fix_sysOfS {N : Nat} (e : Fin N → S.C) : ∀ (s : ObjectSlot S.sig), Term.fragS s = true →
    s.guarded = true →
    ∀ (ρ : List S.C) (emb : Fin (muCS s) → Fin N) (env : Nat → Option (Fin N)),
    (∀ i, i < ρ.length → s.use i ≤ 2) →
    (∀ i, envAt ρ i = envOf e env i) → (∀ i, (envAt ρ i).μ = none) →
    (∀ m, e (emb m) = valsS α β s ρ m) →
    ∀ m, (e (emb m)).f = ((sysOfS α β s emb env m).interp (HS S) e).f
  | .req t, hf, hg, ρ, emb, env, hU, hρ, hμ, hv, m => fix_sysOf e t hf hg ρ emb env hU hρ hμ hv m
  | .optional t, hf, hg, ρ, emb, env, hU, hρ, hμ, hv, m => fix_sysOf e t hf hg ρ emb env hU hρ hμ hv m
  | .fill t _, hf, hg, ρ, emb, env, hU, hρ, hμ, hv, m => fix_sysOf e t hf hg ρ emb env hU hρ hμ hv m

/-- The list form of `fix_sysOf`. -/
theorem fix_sysOfL {N : Nat} (e : Fin N → S.C) : ∀ (ts : List (Term S.sig)), Term.fragL ts = true →
    Term.guardedL ts = true →
    ∀ (ρ : List S.C) (emb : Fin (muCL ts) → Fin N) (env : Nat → Option (Fin N)),
    (∀ i, i < ρ.length → Term.useL i ts ≤ 2) →
    (∀ i, envAt ρ i = envOf e env i) → (∀ i, (envAt ρ i).μ = none) →
    (∀ m, e (emb m) = valsL α β ts ρ m) →
    ∀ m, (e (emb m)).f = ((sysOfL α β ts emb env m).interp (HS S) e).f
  | [], _, _, _, _, _, _, _, _, _, m => m.elim0
  | t :: ts, hf, hg, ρ, emb, env, hU, hρ, hμ, hv, m => by
      simp only [Term.fragL, Bool.and_eq_true] at hf
      simp only [Term.guardedL, Bool.and_eq_true] at hg
      refine Fin.addCases (fun m => ?_) (fun m => ?_) m
      · have := fix_sysOf e t hf.1 hg.1 ρ (fun m => emb (Fin.castAdd _ m)) env
          (fun i hi => le_trans (le_max_left _ _) (hU i hi)) hρ hμ
          (fun m => by have := hv (Fin.castAdd _ m); simpa [valsL] using this) m
        simpa [sysOfL] using this
      · have := fix_sysOfL e ts hf.2 hg.2 ρ (fun m => emb (Fin.natAdd _ m)) env
          (fun i hi => le_trans (le_max_right _ _) (hU i hi)) hρ hμ
          (fun m => by have := hv (Fin.natAdd _ m); simpa [valsL] using this) m
        simpa [sysOfL] using this

/-- The spread form of `fix_sysOf`. -/
theorem fix_sysOfO {N : Nat} (e : Fin N → S.C) : ∀ (sp : Option (Term S.sig)), Term.fragO sp = true →
    Term.guardedO sp = true →
    ∀ (ρ : List S.C) (emb : Fin (muCO sp) → Fin N) (env : Nat → Option (Fin N)),
    (∀ i, i < ρ.length → Term.useO i sp ≤ 2) →
    (∀ i, envAt ρ i = envOf e env i) → (∀ i, (envAt ρ i).μ = none) →
    (∀ m, e (emb m) = valsO α β sp ρ m) →
    ∀ m, (e (emb m)).f = ((sysOfO α β sp emb env m).interp (HS S) e).f
  | none, _, _, _, _, _, _, _, _, _, m => m.elim0
  | some t, hf, hg, ρ, emb, env, hU, hρ, hμ, hv, m => fix_sysOf e t hf hg ρ emb env hU hρ hμ hv m

end

/-- The hoisted system of a closed term: one entry per binder. -/
abbrev hsys (t : Term S.sig) : Fin (muC t) → HFlat S (muC t) := sysOf α β t id noEnv

/-- **The closed term's binder codecs are a fixed point of its hoisted system.** -/
theorem hoist_isFix (t : Term S.sig) (hf : Term.frag t = true) (hg : t.guarded = true) :
    IsFix (sysB (HS S) (hsys α β t)) (vals α β t []) :=
  fun m => fix_sysOf α β _ t hf hg [] id noEnv (fun _ h => absurd h (Nat.not_lt_zero _))
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) m

/-- A codec of the form of a `solve` entry: its held set is its write domain, and its member is
    `⊤`. -/
def MuForm {V M : Type} (c : Codec V M) : Prop := (∀ v, c.T v = ((c.e v).isSome = true)) ∧ c.μ = none

mutual

/-- The codec of each binder has the form of a `solve` entry. -/
theorem vals_muForm : ∀ (t : Term S.sig) (ρ : List S.C) (m : Fin (muC t)), MuForm (vals α β t ρ m)
  | .mu b, ρ, m => by
      change Fin (muC b + 1) at m
      cases m using Fin.cases with
      | zero => exact ⟨fun _ => rfl, rfl⟩
      | succ m =>
        show MuForm (Fin.cons (α := fun _ => S.C) _ _ m.succ)
        rw [Fin.cons_succ]
        exact vals_muForm b _ m
  | .set t, ρ, m => vals_muForm t ρ m
  | .refine t _ _, ρ, m => vals_muForm t ρ m
  | .legacy t _, _, m => vals_muForm t [] m
  | .held _ t P _ _, _, m => by
      refine Fin.addCases (fun m => ?_) (fun m => ?_) m
      · simp only [vals, Fin.append_left]; exact vals_muForm t [] m
      · simp only [vals, Fin.append_right]; exact vals_muForm P [] m
  | .union os, ρ, m => valsL_muForm os ρ m
  | .list pre sp suf, ρ, m => by
      refine Fin.addCases (fun m => ?_) (fun m => Fin.addCases (fun m => ?_) (fun m => ?_) m) m
      · simp only [vals, Fin.append_left]; exact valsL_muForm pre ρ m
      · simp only [vals, Fin.append_left, Fin.append_right]; exact valsO_muForm sp ρ m
      · simp only [vals, Fin.append_right]; exact valsL_muForm suf ρ m
  | .prim _, _, m => m.elim0
  | .opaq, _, m => m.elim0
  | .never, _, m => m.elim0
  | .var _, _, m => m.elim0
  | .object (.mk fs f w), ρ, m => by
      refine Fin.addCases (fun m => ?_) (fun m => ?_) m
      · revert m
        refine sumF_cases _ (fun p m => ?_)
        simp only [vals, Fin.append_left, appF_injF]
        exact valsS_muForm (f (kAt fs p)) ρ m
      · simp only [vals, Fin.append_right]; exact valsO_muForm w ρ m

/-- The slot form of `vals_muForm`. -/
theorem valsS_muForm : ∀ (s : ObjectSlot S.sig) (ρ : List S.C) (m : Fin (muCS s)),
    MuForm (valsS α β s ρ m)
  | .req t, ρ, m => vals_muForm t ρ m
  | .optional t, ρ, m => vals_muForm t ρ m
  | .fill t _, ρ, m => vals_muForm t ρ m

/-- The list form of `vals_muForm`. -/
theorem valsL_muForm : ∀ (ts : List (Term S.sig)) (ρ : List S.C) (m : Fin (muCL ts)),
    MuForm (valsL α β ts ρ m)
  | [], _, m => m.elim0
  | t :: ts, ρ, m => by
      refine Fin.addCases (fun m => ?_) (fun m => ?_) m
      · simp only [valsL, Fin.append_left]; exact vals_muForm t ρ m
      · simp only [valsL, Fin.append_right]; exact valsL_muForm ts ρ m

/-- The spread form of `vals_muForm`. -/
theorem valsO_muForm : ∀ (sp : Option (Term S.sig)) (ρ : List S.C) (m : Fin (muCO sp)),
    MuForm (valsO α β sp ρ m)
  | none, _, m => m.elim0
  | some t, ρ, m => vals_muForm t ρ m

end

end THoistLaws

/-! ### The hoisted system passes the guard of a DAG of scopes

An unguarded edge lowers the rank `rkOf`. Every edge keeps or raises the wall depth of the entry, and an
edge below a wall raises it. So no wall edge reaches back. -/

section THoistOrder
variable {S : Syn} [Sem S] (α : Table S) (β : Table S.op)

/-! The rank of each binder, at depth `d` with `c` binders since the last guard. Below a wall,
    the count starts again. -/
mutual
def rkOf (N : Nat) : (t : Term S.sig) → Nat → Nat → Fin (muC t) → Nat
  | .mu b, d, c => Fin.cons ((d - c) * (N + 1) + (N - d)) (rkOf N b (d + 1) (c + 1))
  | .set t, d, _ => rkOf N t d 0
  | .refine t _ _, d, c => rkOf N t d c
  | .legacy t _, _, _ => rkOf N t 0 0
  | .held _ t P _ _, _, _ => Fin.append (rkOf N t 0 0) (rkOf N P 0 0)
  | .union os, d, c => rkOfL N os d c
  | .list pre sp suf, d, _ =>
      Fin.append (rkOfL N pre d 0) (Fin.append (rkOfO N sp d 0) (rkOfL N suf d 0))
  | .object (.mk fs f w), d, _ =>
      Fin.append (appF (fun p => muCS (f (kAt fs p))) fun p => rkOfS N (f (kAt fs p)) d 0) (rkOfO N w d 0)
  | .prim _, _, _ | .opaq, _, _ | .never, _, _ | .var _, _, _ => Fin.elim0
def rkOfS (N : Nat) : (s : ObjectSlot S.sig) → Nat → Nat → Fin (muCS s) → Nat
  | .req t, d, c => rkOf N t d c
  | .optional t, d, c => rkOf N t d c
  | .fill t _, d, c => rkOf N t d c
def rkOfL (N : Nat) : (ts : List (Term S.sig)) → Nat → Nat → Fin (muCL ts) → Nat
  | [], _, _ => Fin.elim0
  | t :: ts, d, c => Fin.append (rkOf N t d c) (rkOfL N ts d c)
def rkOfO (N : Nat) : (sp : Option (Term S.sig)) → Nat → Nat → Fin (muCO sp) → Nat
  | none, _, _ => Fin.elim0
  | some t, d, c => rkOf N t d c
end

/-- The bottom has no unguarded leaf. -/
theorem ulv_neverF {N : Nat} {j : Fin N} : (neverF (S := S)).ulv (HS S) j = false := by
  cases h : (neverF (S := S)).ulv (HS S) j
  · rfl
  · obtain ⟨_, p, _⟩ := Flat.ulv_node_iff.mp h; exact p.elim0

/-- A larger subtrahend gives a smaller product. -/
theorem sub_mul_le {d i c N : Nat} (h : c ≤ i) : (d - i) * (N + 1) ≤ (d - c) * (N + 1) :=
  Nat.mul_le_mul_right _ (Nat.sub_le_sub_left h d)

mutual

/-- **An unguarded leaf of a hoisted term** has a rank at most the band of the current block. -/
theorem ulv_hoist {N : Nat} (R : Fin N → Nat) : ∀ (t : Term S.sig), Term.frag t = true →
    ∀ (d c : Nat) (emb : Fin (muC t) → Fin N) (env : Nat → Option (Fin N)),
    (∀ m, R (emb m) = rkOf N t d c m) → (∀ i j, env i = some j → R j < (d - i) * (N + 1)) →
    (∀ i, i < c → t.use i ≤ 1) →
    ∀ j, (hoist α β t emb env).ulv (HS S) j = true → R j ≤ (d - c) * (N + 1) + (N - d)
  | .prim _, _, _, _, _, _, _, _, _, _, h => by
      obtain ⟨_, p, _⟩ := Flat.ulv_node_iff.mp h; exact p.elim0
  | .opaq, _, _, _, _, _, _, _, _, _, h => by
      obtain ⟨_, p, _⟩ := Flat.ulv_node_iff.mp h; exact p.elim0
  | .never, _, _, _, _, _, _, _, _, _, h => by
      obtain ⟨_, p, _⟩ := Flat.ulv_node_iff.mp h; exact p.elim0
  | .var i, _, d, c, _, env, _, h2, h3, j, h => by
      simp only [hoist] at h
      cases hi : env i with
      | none => rw [hi, ulv_neverF] at h; exact nomatch h
      | some j' =>
        rw [hi] at h
        simp only [Flat.ulv, decide_eq_true_eq] at h
        subst h
        rcases Nat.lt_or_ge i c with hic | hic
        · have := h3 i hic
          simp [Term.use] at this
        · have h4 := h2 i j' hi
          have h5 := sub_mul_le (d := d) (N := N) hic
          omega
  | .mu b, _, d, c, emb, _, h1, _, _, j, h => by
      simp only [hoist, Flat.ulv, decide_eq_true_eq] at h
      subst h
      exact le_of_eq (h1 _)
  | .set _, _, _, _, _, _, _, _, _, _, h => by
      obtain ⟨hk, _⟩ := Flat.ulv_node_iff.mp h; exact nomatch hk
  | .list _ _ _, _, _, _, _, _, _, _, _, _, h => by
      obtain ⟨hk, _⟩ := Flat.ulv_node_iff.mp h; exact nomatch hk
  | .legacy _ _, _, _, _, _, _, _, _, _, _, h => by
      obtain ⟨hk, _⟩ := Flat.ulv_node_iff.mp h; exact nomatch hk
  | .held .., _, _, _, _, _, _, _, _, _, h => by
      obtain ⟨hk, _⟩ := Flat.ulv_node_iff.mp h; exact nomatch hk
  | .refine t _ _, hf, d, c, emb, env, h1, h2, h3, j, h => by
      obtain ⟨_, _, hp⟩ := Flat.ulv_node_iff.mp h
      exact ulv_hoist R t hf d c emb env h1 h2 h3 j hp
  | .union os, hf, d, c, emb, env, h1, h2, h3, j, h => by
      obtain ⟨_, p, hp⟩ := Flat.ulv_node_iff.mp h
      exact ulv_hoistL R os hf d c emb env h1 h2 h3 p j hp
  | .object (.mk _ _ _), _, _, _, _, _, _, _, _, _, h => by
      obtain ⟨hk, _⟩ := Flat.ulv_node_iff.mp h; exact nomatch hk

/-- The list form of `ulv_hoist`. -/
theorem ulv_hoistL {N : Nat} (R : Fin N → Nat) : ∀ (ts : List (Term S.sig)), Term.fragL ts = true →
    ∀ (d c : Nat) (emb : Fin (muCL ts) → Fin N) (env : Nat → Option (Fin N)),
    (∀ m, R (emb m) = rkOfL N ts d c m) → (∀ i j, env i = some j → R j < (d - i) * (N + 1)) →
    (∀ i, i < c → Term.useL i ts ≤ 1) →
    ∀ p j, (hoistL α β ts emb env p).ulv (HS S) j = true → R j ≤ (d - c) * (N + 1) + (N - d)
  | [], _, _, _, _, _, _, _, _, p, _, _ => p.elim0
  | t :: ts, hf, d, c, emb, env, h1, h2, h3, p, j, h => by
      simp only [Term.fragL, Bool.and_eq_true] at hf
      cases p using Fin.cases with
      | zero =>
        exact ulv_hoist R t hf.1 d c _ env (fun m => (h1 _).trans (Fin.append_left _ _ _)) h2
          (fun i hi => le_trans (le_max_left _ _) (h3 i hi)) j h
      | succ p =>
        exact ulv_hoistL R ts hf.2 d c _ env (fun m => (h1 _).trans (Fin.append_right _ _ _)) h2
          (fun i hi => le_trans (le_max_right _ _) (h3 i hi)) p j h

end

/-- The empty environment names no entry. -/
theorem noEnv_none {N : Nat} {i : Nat} {j : Fin N} : noEnv i ≠ some j := nofun

mutual

/-- **Each unguarded edge of the hoisted system lowers the rank.** -/
theorem rank_sysOf {N : Nat} (R : Fin N → Nat) : ∀ (t : Term S.sig), Term.frag t = true →
    t.guarded = true → ∀ (d c : Nat) (emb : Fin (muC t) → Fin N) (env : Nat → Option (Fin N)),
    (∀ m, R (emb m) = rkOf N t d c m) → (∀ i j, env i = some j → R j < (d - i) * (N + 1)) →
    (∀ i, i < c → t.use i ≤ 1) → d + muC t ≤ N →
    ∀ m j, (sysOf α β t emb env m).ulv (HS S) j = true → R j < R (emb m)
  | .mu b, hf, hg, d, c, emb, env, h1, h2, h3, h4, m, j, h => by
      simp only [Term.guarded, Bool.and_eq_true, decide_eq_true_eq] at hg
      have h0 : R (emb ⟨0, Nat.succ_pos _⟩) = (d - c) * (N + 1) + (N - d) := h1 _
      have h1' : ∀ m, R (emb m.succ) = rkOf N b (d + 1) (c + 1) m := fun m =>
        (h1 m.succ).trans (Fin.cons_succ _ _ _)
      have h2' : ∀ i j, consEnv (emb ⟨0, Nat.succ_pos _⟩) env i = some j →
          R j < (d + 1 - i) * (N + 1) := fun i j hj => match i with
        | 0 => by
          simp only [consEnv, Option.some.injEq] at hj
          subst hj
          rw [h0, Nat.sub_zero, Nat.succ_mul]
          have := Nat.mul_le_mul_right (N + 1) (Nat.sub_le d c)
          omega
        | i + 1 => by
          rw [Nat.add_sub_add_right]
          exact h2 i j hj
      have h3' : ∀ i, i < c + 1 → b.use i ≤ 1 := fun i hi => match i with
        | 0 => hg.1
        | i + 1 => h3 i (by omega)
      change Fin (muC b + 1) at m
      have h4' : d + 1 + muC b ≤ N := by
        have : muC (Term.mu b) = muC b + 1 := rfl
        omega
      cases m using Fin.cases with
      | zero =>
        have := ulv_hoist α β R b hf (d + 1) (c + 1) _ _ h1' h2' h3' j h
        rw [Nat.add_sub_add_right] at this
        show R j < R (emb ⟨0, Nat.succ_pos _⟩)
        rw [h0]
        omega
      | succ m => exact rank_sysOf R b hf hg.2 (d + 1) (c + 1) _ _ h1' h2' h3' h4' m j h
  | .set t, hf, hg, d, _, emb, env, h1, h2, _, h4, m, j, h =>
      rank_sysOf R t hf hg d 0 emb env h1 h2 (fun _ hi => absurd hi (Nat.not_lt_zero _)) h4 m j h
  | .refine t _ _, hf, hg, d, c, emb, env, h1, h2, h3, h4, m, j, h =>
      rank_sysOf R t hf hg d c emb env h1 h2 h3 h4 m j h
  | .legacy t _, hf, hg, d, _, emb, _, h1, _, _, h4, m, j, h =>
      rank_sysOf R t hf hg 0 0 emb noEnv h1 (fun _ _ h => absurd h noEnv_none)
        (fun _ hi => absurd hi (Nat.not_lt_zero _)) (by
          have : muC (Term.legacy t ‹_›) = muC t := rfl
          omega) m j h
  | .held _ t P _ _, hf, hg, d, _, emb, _, h1, _, _, h4, m, j, h => by
      simp only [Term.frag, Bool.and_eq_true] at hf
      simp only [Term.guarded, Bool.and_eq_true] at hg
      have h4e : muC (Term.held ‹_› t P ‹_› ‹_›) = muC t + muC P := rfl
      revert h
      refine Fin.addCases (fun m₁ => ?_) (fun m₂ => ?_) m
      · intro h
        exact rank_sysOf R t hf.1 hg.1 0 0 (fun m => emb (Fin.castAdd _ m)) noEnv
          (fun m => (h1 _).trans (by simp [rkOf])) (fun _ _ h => absurd h noEnv_none)
          (fun _ hi => absurd hi (Nat.not_lt_zero _)) (by omega) m₁ j (by simpa [sysOf] using h)
      · intro h
        exact rank_sysOf R P hf.2 hg.2 0 0 (fun m => emb (Fin.natAdd _ m)) noEnv
          (fun m => (h1 _).trans (by simp [rkOf])) (fun _ _ h => absurd h noEnv_none)
          (fun _ hi => absurd hi (Nat.not_lt_zero _)) (by omega) m₂ j (by simpa [sysOf] using h)
  | .union os, hf, hg, d, c, emb, env, h1, h2, h3, h4, m, j, h =>
      rank_sysOfL R os hf hg d c emb env h1 h2 h3 h4 m j h
  | .list pre sp suf, hf, hg, d, _, emb, env, h1, h2, _, h4, m, j, h => by
      simp only [Term.frag, Bool.and_eq_true] at hf
      simp only [Term.guarded, Bool.and_eq_true] at hg
      have h4e : muC (Term.list pre sp suf) = muCL pre + (muCO sp + muCL suf) := rfl
      revert h
      refine Fin.addCases (fun m₁ => ?_) (fun m₂ => Fin.addCases (fun m₃ => ?_) (fun m₄ => ?_) m₂) m
      · intro h
        exact rank_sysOfL R pre hf.1.1 hg.1.1 d 0 (fun m => emb (Fin.castAdd _ m)) env
          (fun m => (h1 _).trans (by simp [rkOf])) h2 (fun _ hi => absurd hi (Nat.not_lt_zero _))
          (by omega) m₁ j (by simpa [sysOf] using h)
      · intro h
        exact rank_sysOfO R sp hf.1.2 hg.1.2 d 0 (fun m => emb (Fin.natAdd _ (Fin.castAdd _ m))) env
          (fun m => (h1 _).trans (by simp [rkOf])) h2 (fun _ hi => absurd hi (Nat.not_lt_zero _))
          (by omega) m₃ j (by simpa [sysOf] using h)
      · intro h
        exact rank_sysOfL R suf hf.2 hg.2 d 0 (fun m => emb (Fin.natAdd _ (Fin.natAdd _ m))) env
          (fun m => (h1 _).trans (by simp [rkOf])) h2 (fun _ hi => absurd hi (Nat.not_lt_zero _))
          (by omega) m₄ j (by simpa [sysOf] using h)
  | .prim _, _, _, _, _, _, _, _, _, _, _, m, _, _ => m.elim0
  | .opaq, _, _, _, _, _, _, _, _, _, _, m, _, _ => m.elim0
  | .never, _, _, _, _, _, _, _, _, _, _, m, _, _ => m.elim0
  | .var _, _, _, _, _, _, _, _, _, _, _, m, _, _ => m.elim0
  | .object (.mk fs f w), hf, hg, d, _, emb, env, h1, h2, _, h4, m, j, h => by
      simp only [Term.frag, Bool.and_eq_true, decide_eq_true_eq] at hf
      simp only [Term.guarded, Body.guarded, Bool.and_eq_true, decide_eq_true_eq] at hg
      have h4e : muC (Term.object (.mk fs f w)) =
          sumF _ (fun p => muCS (f (kAt fs p))) + muCO w := rfl
      revert h
      refine Fin.addCases (fun m => ?_) (fun m => ?_) m
      · revert m
        refine sumF_cases _ (fun p m => ?_)
        intro h
        have hle := le_sumF (fun p => muCS (f (kAt fs p))) p
        exact rank_sysOfS R (f (kAt fs p)) (hf.1 _) (hg.1 _) d 0
          (fun m => emb (Fin.castAdd _ (injF (fun p => muCS (f (kAt fs p))) p m))) env
          (fun m => (h1 _).trans (by simp [rkOf, appF_injF])) h2
          (fun _ hi => absurd hi (Nat.not_lt_zero _)) (by omega) m j (by simpa [sysOf, appF_injF] using h)
      · intro h
        exact rank_sysOfO R w hf.2 hg.2 d 0 (fun m => emb (Fin.natAdd _ m)) env
          (fun m => (h1 _).trans (by simp [rkOf])) h2 (fun _ hi => absurd hi (Nat.not_lt_zero _))
          (by omega) m j (by simpa [sysOf] using h)

/-- The slot form of `rank_sysOf`. -/
theorem rank_sysOfS {N : Nat} (R : Fin N → Nat) : ∀ (s : ObjectSlot S.sig), Term.fragS s = true →
    s.guarded = true → ∀ (d c : Nat) (emb : Fin (muCS s) → Fin N) (env : Nat → Option (Fin N)),
    (∀ m, R (emb m) = rkOfS N s d c m) → (∀ i j, env i = some j → R j < (d - i) * (N + 1)) →
    (∀ i, i < c → s.use i ≤ 1) → d + muCS s ≤ N →
    ∀ m j, (sysOfS α β s emb env m).ulv (HS S) j = true → R j < R (emb m)
  | .req t, hf, hg, d, c, emb, env, h1, h2, h3, h4, m, j, h => rank_sysOf R t hf hg d c emb env h1 h2 h3 h4 m j h
  | .optional t, hf, hg, d, c, emb, env, h1, h2, h3, h4, m, j, h =>
      rank_sysOf R t hf hg d c emb env h1 h2 h3 h4 m j h
  | .fill t _, hf, hg, d, c, emb, env, h1, h2, h3, h4, m, j, h =>
      rank_sysOf R t hf hg d c emb env h1 h2 h3 h4 m j h

/-- The list form of `rank_sysOf`. -/
theorem rank_sysOfL {N : Nat} (R : Fin N → Nat) : ∀ (ts : List (Term S.sig)), Term.fragL ts = true →
    Term.guardedL ts = true → ∀ (d c : Nat) (emb : Fin (muCL ts) → Fin N) (env : Nat → Option (Fin N)),
    (∀ m, R (emb m) = rkOfL N ts d c m) → (∀ i j, env i = some j → R j < (d - i) * (N + 1)) →
    (∀ i, i < c → Term.useL i ts ≤ 1) → d + muCL ts ≤ N →
    ∀ m j, (sysOfL α β ts emb env m).ulv (HS S) j = true → R j < R (emb m)
  | [], _, _, _, _, _, _, _, _, _, _, m, _, _ => m.elim0
  | t :: ts, hf, hg, d, c, emb, env, h1, h2, h3, h4, m, j, h => by
      simp only [Term.fragL, Bool.and_eq_true] at hf
      simp only [Term.guardedL, Bool.and_eq_true] at hg
      have h4e : muCL (t :: ts) = muC t + muCL ts := rfl
      revert h
      refine Fin.addCases (fun m₁ => ?_) (fun m₂ => ?_) m
      · intro h
        exact rank_sysOf R t hf.1 hg.1 d c (fun m => emb (Fin.castAdd _ m)) env
          (fun m => (h1 _).trans (by simp [rkOfL])) h2
          (fun i hi => le_trans (le_max_left _ _) (h3 i hi)) (by omega) m₁ j
          (by simpa [sysOfL] using h)
      · intro h
        exact rank_sysOfL R ts hf.2 hg.2 d c (fun m => emb (Fin.natAdd _ m)) env
          (fun m => (h1 _).trans (by simp [rkOfL])) h2
          (fun i hi => le_trans (le_max_right _ _) (h3 i hi)) (by omega) m₂ j
          (by simpa [sysOfL] using h)

/-- The spread form of `rank_sysOf`. -/
theorem rank_sysOfO {N : Nat} (R : Fin N → Nat) : ∀ (sp : Option (Term S.sig)), Term.fragO sp = true →
    Term.guardedO sp = true → ∀ (d c : Nat) (emb : Fin (muCO sp) → Fin N) (env : Nat → Option (Fin N)),
    (∀ m, R (emb m) = rkOfO N sp d c m) → (∀ i j, env i = some j → R j < (d - i) * (N + 1)) →
    (∀ i, i < c → Term.useO i sp ≤ 1) → d + muCO sp ≤ N →
    ∀ m j, (sysOfO α β sp emb env m).ulv (HS S) j = true → R j < R (emb m)
  | none, _, _, _, _, _, _, _, _, _, _, m, _, _ => m.elim0
  | some t, hf, hg, d, c, emb, env, h1, h2, h3, h4, m, j, h =>
      rank_sysOf R t hf hg d c emb env h1 h2 h3 h4 m j h

end



/-! The wall depth of each binder: the number of walls above it. -/
mutual
def wdOf : (t : Term S.sig) → Nat → Fin (muC t) → Nat
  | .mu b, w => Fin.cons w (wdOf b w)
  | .set t, w => wdOf t w
  | .refine t _ _, w => wdOf t w
  | .legacy t _, w => wdOf t (w + 1)
  | .held _ t P _ _, w => Fin.append (wdOf t (w + 1)) (wdOf P (w + 1))
  | .union os, w => wdOfL os w
  | .list pre sp suf, w => Fin.append (wdOfL pre w) (Fin.append (wdOfO sp w) (wdOfL suf w))
  | .object (.mk fs f wd), w =>
      Fin.append (appF (fun p => muCS (f (kAt fs p))) fun p => wdOfS (f (kAt fs p)) w) (wdOfO wd w)
  | .prim _, _ | .opaq, _ | .never, _ | .var _, _ => Fin.elim0
def wdOfS : (s : ObjectSlot S.sig) → Nat → Fin (muCS s) → Nat
  | .req t, w => wdOf t w
  | .optional t, w => wdOf t w
  | .fill t _, w => wdOf t w
def wdOfL : (ts : List (Term S.sig)) → Nat → Fin (muCL ts) → Nat
  | [], _ => Fin.elim0
  | t :: ts, w => Fin.append (wdOf t w) (wdOfL ts w)
def wdOfO : (sp : Option (Term S.sig)) → Nat → Fin (muCO sp) → Nat
  | none, _ => Fin.elim0
  | some t, w => wdOf t w
end

/-- A leaf has the leaf `j` exactly where the leaf is `j`. -/
theorem Flat.lv_leaf {Op : Type} {ar : Op → Nat} {N : Nat} {i j : Fin N} :
    (Flat.leaf (Op := Op) (arity := ar) i).lv j = true ↔ i = j := by
  simp [Flat.lv]

/-- The bottom has no leaf. -/
theorem lv_neverF {N : Nat} {j : Fin N} : (neverF (S := S)).lv j = false := by
  cases h : (neverF (S := S)).lv j
  · rfl
  · obtain ⟨p, _⟩ := Flat.lv_node.mp h; exact p.elim0

mutual

/-- **A leaf of a hoisted term** has a wall depth at least the current one. -/
theorem lv_hoist {N : Nat} (W : Fin N → Nat) : ∀ (t : Term S.sig), Term.frag t = true →
    ∀ (w : Nat) (emb : Fin (muC t) → Fin N) (env : Nat → Option (Fin N)),
    (∀ m, W (emb m) = wdOf t w m) → (∀ i j, env i = some j → w ≤ W j) →
    ∀ j, (hoist α β t emb env).lv j = true → w ≤ W j
  | .prim _, _, _, _, _, _, _, _, h => by obtain ⟨p, _⟩ := Flat.lv_node.mp h; exact p.elim0
  | .opaq, _, _, _, _, _, _, _, h => by obtain ⟨p, _⟩ := Flat.lv_node.mp h; exact p.elim0
  | .never, _, _, _, _, _, _, _, h => by obtain ⟨p, _⟩ := Flat.lv_node.mp h; exact p.elim0
  | .var i, _, w, _, env, _, h2, j, h => by
      simp only [hoist] at h
      cases hi : env i with
      | none => rw [hi, lv_neverF] at h; exact nomatch h
      | some j' =>
        rw [hi, Flat.lv_leaf] at h
        subst h
        exact h2 i j' hi
  | .mu b, _, w, emb, _, h1, _, j, h => by
      simp only [hoist, Flat.lv_leaf] at h
      subst h
      exact le_of_eq (h1 ⟨0, Nat.succ_pos _⟩).symm
  | .set t, hf, w, emb, env, h1, h2, j, h => by
      obtain ⟨_, hp⟩ := Flat.lv_node.mp h
      exact lv_hoist W t hf w emb env h1 h2 j hp
  | .refine t _ _, hf, w, emb, env, h1, h2, j, h => by
      obtain ⟨_, hp⟩ := Flat.lv_node.mp h
      exact lv_hoist W t hf w emb env h1 h2 j hp
  | .legacy t _, hf, w, emb, _, h1, _, j, h => by
      obtain ⟨_, hp⟩ := Flat.lv_node.mp h
      exact Nat.le_of_succ_le (lv_hoist W t hf (w + 1) emb noEnv h1 (fun _ _ h => absurd h noEnv_none) j hp)
  | .held _ t P _ _, hf, w, emb, _, h1, _, j, h => by
      simp only [Term.frag, Bool.and_eq_true] at hf
      obtain ⟨⟨p, hpl⟩, hp⟩ := Flat.lv_node.mp h
      match p, hpl, hp with
      | 0, _, hp =>
        exact Nat.le_of_succ_le (lv_hoist W t hf.1 (w + 1) (fun m => emb (Fin.castAdd _ m))
          noEnv (fun m => (h1 _).trans (by simp [wdOf])) (fun _ _ h => absurd h noEnv_none) j hp)
      | 1, _, hp =>
        exact Nat.le_of_succ_le (lv_hoist W P hf.2 (w + 1) (fun m => emb (Fin.natAdd _ m))
          noEnv (fun m => (h1 _).trans (by simp [wdOf])) (fun _ _ h => absurd h noEnv_none) j hp)
      | k + 2, hpl, _ => exact absurd hpl (by change ¬ (k + 2 < 2); omega)
  | .union os, hf, w, emb, env, h1, h2, j, h => by
      obtain ⟨p, hp⟩ := Flat.lv_node.mp h
      exact lv_hoistL W os hf w emb env h1 h2 p j hp
  | .list pre sp suf, hf, w, emb, env, h1, h2, j, h => by
      simp only [Term.frag, Bool.and_eq_true] at hf
      obtain ⟨p, hp⟩ := Flat.lv_node.mp h
      revert hp
      refine Fin.addCases (fun p => ?_) (fun p => Fin.addCases (fun p => ?_) (fun p => ?_) p) p
      · intro hp
        exact lv_hoistL W pre hf.1.1 w (fun m => emb (Fin.castAdd _ m)) env (fun m => (h1 _).trans (by simp [wdOf])) h2 p j
          (by simpa using hp)
      · intro hp
        exact lv_hoistO W sp hf.1.2 w (fun m => emb (Fin.natAdd _ (Fin.castAdd _ m))) env (fun m => (h1 _).trans (by simp [wdOf])) h2 p j
          (by simpa using hp)
      · intro hp
        exact lv_hoistL W suf hf.2 w (fun m => emb (Fin.natAdd _ (Fin.natAdd _ m))) env (fun m => (h1 _).trans (by simp [wdOf])) h2 p j
          (by simpa using hp)
  | .object (.mk fs f wd), hf, w, emb, env, h1, h2, j, h => by
      simp only [Term.frag, Bool.and_eq_true, decide_eq_true_eq] at hf
      obtain ⟨p, hp⟩ := Flat.lv_node.mp h
      revert hp
      refine Fin.addCases (fun p => ?_) (fun p => ?_) p
      · intro hp
        exact lv_hoistS W (f (kAt fs p)) (hf.1 _) w
          (fun m => emb (Fin.castAdd _ (injF (fun p => muCS (f (kAt fs p))) p m))) env
          (fun m => (h1 _).trans (by simp [wdOf, appF_injF])) h2 j (by simpa using hp)
      · intro hp
        exact lv_hoistO W wd hf.2 w (fun m => emb (Fin.natAdd _ m)) env
          (fun m => (h1 _).trans (by simp [wdOf])) h2 p j (by simpa using hp)

/-- The slot form of `lv_hoist`. -/
theorem lv_hoistS {N : Nat} (W : Fin N → Nat) : ∀ (s : ObjectSlot S.sig), Term.fragS s = true →
    ∀ (w : Nat) (emb : Fin (muCS s) → Fin N) (env : Nat → Option (Fin N)),
    (∀ m, W (emb m) = wdOfS s w m) → (∀ i j, env i = some j → w ≤ W j) →
    ∀ j, (hoistS α β s emb env).lv j = true → w ≤ W j
  | .req t, hf, w, emb, env, h1, h2, j, h => lv_hoist W t hf w emb env h1 h2 j h
  | .optional t, hf, w, emb, env, h1, h2, j, h => lv_hoist W t hf w emb env h1 h2 j h
  | .fill t _, hf, w, emb, env, h1, h2, j, h => lv_hoist W t hf w emb env h1 h2 j h

/-- The list form of `lv_hoist`. -/
theorem lv_hoistL {N : Nat} (W : Fin N → Nat) : ∀ (ts : List (Term S.sig)), Term.fragL ts = true →
    ∀ (w : Nat) (emb : Fin (muCL ts) → Fin N) (env : Nat → Option (Fin N)),
    (∀ m, W (emb m) = wdOfL ts w m) → (∀ i j, env i = some j → w ≤ W j) →
    ∀ p j, (hoistL α β ts emb env p).lv j = true → w ≤ W j
  | [], _, _, _, _, _, _, p, _, _ => p.elim0
  | t :: ts, hf, w, emb, env, h1, h2, p, j, h => by
      simp only [Term.fragL, Bool.and_eq_true] at hf
      cases p using Fin.cases with
      | zero =>
        exact lv_hoist W t hf.1 w _ env (fun m => (h1 _).trans (Fin.append_left _ _ _)) h2 j h
      | succ p =>
        exact lv_hoistL W ts hf.2 w _ env (fun m => (h1 _).trans (Fin.append_right _ _ _)) h2 p j h

/-- The spread form of `lv_hoist`. -/
theorem lv_hoistO {N : Nat} (W : Fin N → Nat) : ∀ (sp : Option (Term S.sig)), Term.fragO sp = true →
    ∀ (w : Nat) (emb : Fin (muCO sp) → Fin N) (env : Nat → Option (Fin N)),
    (∀ m, W (emb m) = wdOfO sp w m) → (∀ i j, env i = some j → w ≤ W j) →
    ∀ p j, (hoistO α β sp emb env p).lv j = true → w ≤ W j
  | none, _, _, _, _, _, _, p, _, _ => p.elim0
  | some t, hf, w, emb, env, h1, h2, _, j, h => lv_hoist W t hf w emb env h1 h2 j h

end

mutual

/-- **A leaf below a wall of a hoisted term** has a wall depth above the current one. -/
theorem wlv_hoist {N : Nat} (W : Fin N → Nat) : ∀ (t : Term S.sig), Term.frag t = true →
    ∀ (w : Nat) (emb : Fin (muC t) → Fin N) (env : Nat → Option (Fin N)),
    (∀ m, W (emb m) = wdOf t w m) →
    ∀ j, (hoist α β t emb env).wlv (HS S) j = true → w < W j
  | .prim _, _, _, _, _, _, _, h => by
      rcases Flat.wlv_node.mp h with ⟨_, p, _⟩ | ⟨_, p, _⟩ <;> exact p.elim0
  | .opaq, _, _, _, _, _, _, h => by
      rcases Flat.wlv_node.mp h with ⟨_, p, _⟩ | ⟨_, p, _⟩ <;> exact p.elim0
  | .never, _, _, _, _, _, _, h => by
      rcases Flat.wlv_node.mp h with ⟨_, p, _⟩ | ⟨_, p, _⟩ <;> exact p.elim0
  | .var i, _, _, _, env, _, j, h => by
      simp only [hoist] at h
      cases hi : env i with
      | none =>
        rw [hi] at h
        rcases Flat.wlv_node.mp h with ⟨_, p, _⟩ | ⟨_, p, _⟩ <;> exact p.elim0
      | some j' => rw [hi] at h; simp [Flat.wlv] at h
  | .mu b, _, _, _, _, _, _, h => by simp [hoist, Flat.wlv] at h
  | .set t, hf, w, emb, env, h1, j, h => by
      rcases Flat.wlv_node.mp h with ⟨hk, _⟩ | ⟨_, _, hp⟩
      · exact nomatch hk
      · exact wlv_hoist W t hf w emb env h1 j hp
  | .refine t _ _, hf, w, emb, env, h1, j, h => by
      rcases Flat.wlv_node.mp h with ⟨hk, _⟩ | ⟨_, _, hp⟩
      · exact nomatch hk
      · exact wlv_hoist W t hf w emb env h1 j hp
  | .legacy t _, hf, w, emb, _, h1, j, h => by
      rcases Flat.wlv_node.mp h with ⟨_, _, hp⟩ | ⟨hk, _⟩
      · exact lv_hoist α β W t hf (w + 1) emb noEnv h1 (fun _ _ h => absurd h noEnv_none) j hp
      · exact absurd rfl hk
  | .held _ t P _ _, hf, w, emb, _, h1, j, h => by
      simp only [Term.frag, Bool.and_eq_true] at hf
      rcases Flat.wlv_node.mp h with ⟨_, ⟨p, hpl⟩, hp⟩ | ⟨hk, _⟩
      · match p, hpl, hp with
        | 0, _, hp =>
          exact lv_hoist α β W t hf.1 (w + 1) (fun m => emb (Fin.castAdd _ m)) noEnv
            (fun m => (h1 _).trans (by simp [wdOf])) (fun _ _ h => absurd h noEnv_none) j hp
        | 1, _, hp =>
          exact lv_hoist α β W P hf.2 (w + 1) (fun m => emb (Fin.natAdd _ m)) noEnv
            (fun m => (h1 _).trans (by simp [wdOf])) (fun _ _ h => absurd h noEnv_none) j hp
        | k + 2, hpl, _ => exact absurd hpl (by change ¬ (k + 2 < 2); omega)
      · exact absurd rfl hk
  | .union os, hf, w, emb, env, h1, j, h => by
      rcases Flat.wlv_node.mp h with ⟨hk, _⟩ | ⟨_, p, hp⟩
      · exact nomatch hk
      · exact wlv_hoistL W os hf w emb env h1 p j hp
  | .list pre sp suf, hf, w, emb, env, h1, j, h => by
      simp only [Term.frag, Bool.and_eq_true] at hf
      rcases Flat.wlv_node.mp h with ⟨hk, _⟩ | ⟨_, p, hp⟩
      · exact nomatch hk
      revert hp
      refine Fin.addCases (fun p => ?_) (fun p => Fin.addCases (fun p => ?_) (fun p => ?_) p) p
      · intro hp
        exact wlv_hoistL W pre hf.1.1 w (fun m => emb (Fin.castAdd _ m)) env (fun m => (h1 _).trans (by simp [wdOf])) p j
          (by simpa using hp)
      · intro hp
        exact wlv_hoistO W sp hf.1.2 w (fun m => emb (Fin.natAdd _ (Fin.castAdd _ m))) env (fun m => (h1 _).trans (by simp [wdOf])) p j
          (by simpa using hp)
      · intro hp
        exact wlv_hoistL W suf hf.2 w (fun m => emb (Fin.natAdd _ (Fin.natAdd _ m))) env (fun m => (h1 _).trans (by simp [wdOf])) p j
          (by simpa using hp)
  | .object (.mk fs f wd), hf, w, emb, env, h1, j, h => by
      simp only [Term.frag, Bool.and_eq_true, decide_eq_true_eq] at hf
      rcases Flat.wlv_node.mp h with ⟨hk, _⟩ | ⟨_, p, hp⟩
      · exact nomatch hk
      revert hp
      refine Fin.addCases (fun p => ?_) (fun p => ?_) p
      · intro hp
        exact wlv_hoistS W (f (kAt fs p)) (hf.1 _) w
          (fun m => emb (Fin.castAdd _ (injF (fun p => muCS (f (kAt fs p))) p m))) env
          (fun m => (h1 _).trans (by simp [wdOf, appF_injF])) j (by simpa using hp)
      · intro hp
        exact wlv_hoistO W wd hf.2 w (fun m => emb (Fin.natAdd _ m)) env
          (fun m => (h1 _).trans (by simp [wdOf])) p j (by simpa using hp)

/-- The slot form of `wlv_hoist`. -/
theorem wlv_hoistS {N : Nat} (W : Fin N → Nat) : ∀ (s : ObjectSlot S.sig), Term.fragS s = true →
    ∀ (w : Nat) (emb : Fin (muCS s) → Fin N) (env : Nat → Option (Fin N)),
    (∀ m, W (emb m) = wdOfS s w m) →
    ∀ j, (hoistS α β s emb env).wlv (HS S) j = true → w < W j
  | .req t, hf, w, emb, env, h1, j, h => wlv_hoist W t hf w emb env h1 j h
  | .optional t, hf, w, emb, env, h1, j, h => wlv_hoist W t hf w emb env h1 j h
  | .fill t _, hf, w, emb, env, h1, j, h => wlv_hoist W t hf w emb env h1 j h

/-- The list form of `wlv_hoist`. -/
theorem wlv_hoistL {N : Nat} (W : Fin N → Nat) : ∀ (ts : List (Term S.sig)), Term.fragL ts = true →
    ∀ (w : Nat) (emb : Fin (muCL ts) → Fin N) (env : Nat → Option (Fin N)),
    (∀ m, W (emb m) = wdOfL ts w m) →
    ∀ p j, (hoistL α β ts emb env p).wlv (HS S) j = true → w < W j
  | [], _, _, _, _, _, p, _, _ => p.elim0
  | t :: ts, hf, w, emb, env, h1, p, j, h => by
      simp only [Term.fragL, Bool.and_eq_true] at hf
      cases p using Fin.cases with
      | zero =>
        exact wlv_hoist W t hf.1 w _ env (fun m => (h1 _).trans (Fin.append_left _ _ _)) j h
      | succ p =>
        exact wlv_hoistL W ts hf.2 w _ env (fun m => (h1 _).trans (Fin.append_right _ _ _)) p j h

/-- The spread form of `wlv_hoist`. -/
theorem wlv_hoistO {N : Nat} (W : Fin N → Nat) : ∀ (sp : Option (Term S.sig)), Term.fragO sp = true →
    ∀ (w : Nat) (emb : Fin (muCO sp) → Fin N) (env : Nat → Option (Fin N)),
    (∀ m, W (emb m) = wdOfO sp w m) →
    ∀ p j, (hoistO α β sp emb env p).wlv (HS S) j = true → w < W j
  | none, _, _, _, _, _, p, _, _ => p.elim0
  | some t, hf, w, emb, env, h1, _, j, h => wlv_hoist W t hf w emb env h1 j h

end

/-- What the wall depth owes on the edges of an entry. -/
def WdEdges {N : Nat} (W : Fin N → Nat) (x : Fin N) (g : HFlat S N) : Prop :=
  (∀ j, g.lv j = true → W x ≤ W j) ∧ (∀ j, g.wlv (HS S) j = true → W x < W j)

mutual

/-- **Every edge of the hoisted system keeps or raises the wall depth, and an edge below a wall
    raises it.** -/
theorem wd_sysOf {N : Nat} (W : Fin N → Nat) : ∀ (t : Term S.sig), Term.frag t = true →
    ∀ (w : Nat) (emb : Fin (muC t) → Fin N) (env : Nat → Option (Fin N)),
    (∀ m, W (emb m) = wdOf t w m) → (∀ i j, env i = some j → w ≤ W j) →
    ∀ m, WdEdges W (emb m) (sysOf α β t emb env m)
  | .mu b, hf, w, emb, env, h1, h2, m => by
      have h0 : W (emb ⟨0, Nat.succ_pos _⟩) = w := h1 _
      have h1' : ∀ m, W (emb m.succ) = wdOf b w m := fun m => (h1 m.succ).trans (Fin.cons_succ _ _ _)
      have h2' : ∀ i j, consEnv (emb ⟨0, Nat.succ_pos _⟩) env i = some j → w ≤ W j :=
        fun i j hj => match i with
          | 0 => by simp only [consEnv, Option.some.injEq] at hj; subst hj; omega
          | i + 1 => h2 i j hj
      change Fin (muC b + 1) at m
      cases m using Fin.cases with
      | zero =>
        refine ⟨fun j hj => ?_, fun j hj => ?_⟩
        · show W (emb ⟨0, Nat.succ_pos _⟩) ≤ W j
          rw [h0]; exact lv_hoist α β W b hf w _ _ h1' h2' j hj
        · show W (emb ⟨0, Nat.succ_pos _⟩) < W j
          rw [h0]; exact wlv_hoist α β W b hf w _ _ h1' j hj
      | succ m => exact wd_sysOf W b hf w _ _ h1' h2' m
  | .set t, hf, w, emb, env, h1, h2, m => wd_sysOf W t hf w emb env h1 h2 m
  | .refine t _ _, hf, w, emb, env, h1, h2, m => wd_sysOf W t hf w emb env h1 h2 m
  | .legacy t _, hf, w, emb, _, h1, _, m =>
      wd_sysOf W t hf (w + 1) emb noEnv h1 (fun _ _ h => absurd h noEnv_none) m
  | .held _ t P _ _, hf, w, emb, _, h1, _, m => by
      simp only [Term.frag, Bool.and_eq_true] at hf
      refine Fin.addCases (fun m => ?_) (fun m => ?_) m
      · have := wd_sysOf W t hf.1 (w + 1) (fun m => emb (Fin.castAdd _ m)) noEnv
          (fun m => (h1 _).trans (by simp [wdOf])) (fun _ _ h => absurd h noEnv_none) m
        simpa [sysOf] using this
      · have := wd_sysOf W P hf.2 (w + 1) (fun m => emb (Fin.natAdd _ m)) noEnv
          (fun m => (h1 _).trans (by simp [wdOf])) (fun _ _ h => absurd h noEnv_none) m
        simpa [sysOf] using this
  | .union os, hf, w, emb, env, h1, h2, m => wd_sysOfL W os hf w emb env h1 h2 m
  | .list pre sp suf, hf, w, emb, env, h1, h2, m => by
      simp only [Term.frag, Bool.and_eq_true] at hf
      refine Fin.addCases (fun m => ?_) (fun m => Fin.addCases (fun m => ?_) (fun m => ?_) m) m
      · have := wd_sysOfL W pre hf.1.1 w (fun m => emb (Fin.castAdd _ m)) env
          (fun m => (h1 _).trans (by simp [wdOf])) h2 m
        simpa [sysOf] using this
      · have := wd_sysOfO W sp hf.1.2 w (fun m => emb (Fin.natAdd _ (Fin.castAdd _ m))) env
          (fun m => (h1 _).trans (by simp [wdOf])) h2 m
        simpa [sysOf] using this
      · have := wd_sysOfL W suf hf.2 w (fun m => emb (Fin.natAdd _ (Fin.natAdd _ m))) env
          (fun m => (h1 _).trans (by simp [wdOf])) h2 m
        simpa [sysOf] using this
  | .prim _, _, _, _, _, _, _, m => m.elim0
  | .opaq, _, _, _, _, _, _, m => m.elim0
  | .never, _, _, _, _, _, _, m => m.elim0
  | .var _, _, _, _, _, _, _, m => m.elim0
  | .object (.mk fs f wd), hf, w, emb, env, h1, h2, m => by
      simp only [Term.frag, Bool.and_eq_true, decide_eq_true_eq] at hf
      refine Fin.addCases (fun m => ?_) (fun m => ?_) m
      · revert m
        refine sumF_cases _ (fun p m => ?_)
        have := wd_sysOfS W (f (kAt fs p)) (hf.1 _) w
          (fun m => emb (Fin.castAdd _ (injF (fun p => muCS (f (kAt fs p))) p m))) env
          (fun m => (h1 _).trans (by simp [wdOf, appF_injF])) h2 m
        simpa [sysOf, appF_injF] using this
      · have := wd_sysOfO W wd hf.2 w (fun m => emb (Fin.natAdd _ m)) env
          (fun m => (h1 _).trans (by simp [wdOf])) h2 m
        simpa [sysOf] using this

/-- The slot form of `wd_sysOf`. -/
theorem wd_sysOfS {N : Nat} (W : Fin N → Nat) : ∀ (s : ObjectSlot S.sig), Term.fragS s = true →
    ∀ (w : Nat) (emb : Fin (muCS s) → Fin N) (env : Nat → Option (Fin N)),
    (∀ m, W (emb m) = wdOfS s w m) → (∀ i j, env i = some j → w ≤ W j) →
    ∀ m, WdEdges W (emb m) (sysOfS α β s emb env m)
  | .req t, hf, w, emb, env, h1, h2, m => wd_sysOf W t hf w emb env h1 h2 m
  | .optional t, hf, w, emb, env, h1, h2, m => wd_sysOf W t hf w emb env h1 h2 m
  | .fill t _, hf, w, emb, env, h1, h2, m => wd_sysOf W t hf w emb env h1 h2 m

/-- The list form of `wd_sysOf`. -/
theorem wd_sysOfL {N : Nat} (W : Fin N → Nat) : ∀ (ts : List (Term S.sig)), Term.fragL ts = true →
    ∀ (w : Nat) (emb : Fin (muCL ts) → Fin N) (env : Nat → Option (Fin N)),
    (∀ m, W (emb m) = wdOfL ts w m) → (∀ i j, env i = some j → w ≤ W j) →
    ∀ m, WdEdges W (emb m) (sysOfL α β ts emb env m)
  | [], _, _, _, _, _, _, m => m.elim0
  | t :: ts, hf, w, emb, env, h1, h2, m => by
      simp only [Term.fragL, Bool.and_eq_true] at hf
      refine Fin.addCases (fun m => ?_) (fun m => ?_) m
      · have := wd_sysOf W t hf.1 w (fun m => emb (Fin.castAdd _ m)) env
          (fun m => (h1 _).trans (by simp [wdOfL])) h2 m
        simpa [sysOfL] using this
      · have := wd_sysOfL W ts hf.2 w (fun m => emb (Fin.natAdd _ m)) env
          (fun m => (h1 _).trans (by simp [wdOfL])) h2 m
        simpa [sysOfL] using this

/-- The spread form of `wd_sysOf`. -/
theorem wd_sysOfO {N : Nat} (W : Fin N → Nat) : ∀ (sp : Option (Term S.sig)), Term.fragO sp = true →
    ∀ (w : Nat) (emb : Fin (muCO sp) → Fin N) (env : Nat → Option (Fin N)),
    (∀ m, W (emb m) = wdOfO sp w m) → (∀ i j, env i = some j → w ≤ W j) →
    ∀ m, WdEdges W (emb m) (sysOfO α β sp emb env m)
  | none, _, _, _, _, _, _, m => m.elim0
  | some t, hf, w, emb, env, h1, h2, m => wd_sysOf W t hf w emb env h1 h2 m

end

/-- **The hoisted system of a guarded closed term passes the guard of a DAG of scopes.** -/
theorem hoist_dagGuard (t : Term S.sig) (hg : t.guarded = true) :
    DagGuard (HS S) (hsys α β t) := by
  have hf := Term.frag_all t
  refine ⟨noCycle_of_rank (rkOf (muC t) t 0 0) fun i j hij => ?_, fun i j hw hr => ?_⟩
  · exact rank_sysOf α β _ t hf hg 0 0 id noEnv (fun _ => rfl) (fun _ _ h => absurd h noEnv_none)
      (fun _ hi => absurd hi (Nat.not_lt_zero _)) (by omega) i j hij
  · have hwd := wd_sysOf α β (wdOf t 0) t hf 0 id noEnv (fun _ => rfl)
      (fun _ _ h => absurd h noEnv_none)
    have hup : ∀ a b, Relation.ReflTransGen (REdge (hsys α β t)) a b → wdOf t 0 a ≤ wdOf t 0 b := by
      intro a b hab
      induction hab with
      | refl => exact le_rfl
      | tail _ hbc ih => exact le_trans ih ((hwd _).1 _ hbc)
    have h5 : wdOf t 0 i < wdOf t 0 j := (hwd i).2 j hw
    have h6 := hup j i hr
    omega

/-- **The hoist solves a guarded closed term**: the term has an order and a DAG of scopes whose
    graph form is its hoisted system. Each binder's entry of the solution is the binder's codec, the whole codec, and
    the term over the solution is the term's denotation. -/
theorem hoist_solution (t : Term S.sig) (hg : t.guarded = true) :
    ∃ (π : Equiv.Perm (Fin (muC t))) (d : DSys (HS S) (muC t)),
      (∀ m, d.graph m = (hsys α β t (π.symm m)).bind fun j => .leaf (π j)) ∧
      (∀ m, d.sol Mean.d (π m) = vals α β t [] m) ∧
      (hoist α β t (fun m => π m) noEnv).interp (HS S) (d.sol Mean.d) = denote α β t [] := by
  have hf := Term.frag_all t
  obtain ⟨π, d, hrel⟩ := dsys_of_guard (hoist_dagGuard α β t hg)
  have h1 : IsFix (sysB (HS S) (hsys α β t)) fun i => vals α β t [] (π.symm (π i)) := by
    simpa using hoist_isFix α β t hf hg
  have h2 := (isFix_rename π hrel fun m => vals α β t [] (π.symm m)).mpr h1
  have h3 : ∀ m, d.sol Mean.d (π m) = vals α β t [] m := fun m => by
    have := (dsys_solution Mean.d_pos HS_lawful HS_wallF d).2 _ h2 (π m)
    simp only [Equiv.symm_apply_apply] at this
    exact DSys.sol_eq d (π m) (vals_muForm α β t [] m).1 (vals_muForm α β t [] m).2 this.symm
  exact ⟨π, d, hrel, h3, interp_hoist α β _ t hf hg [] _ noEnv
    (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ => rfl) (fun _ => rfl) h3⟩

/-- At a closed binder, the entry of the binder in the solution is its denotation. -/
theorem hoist_mu (b : Term S.sig) (hg : (Term.mu b).guarded = true) :
    ∃ (π : Equiv.Perm (Fin (muC (Term.mu b)))) (d : DSys (HS S) (muC (Term.mu b))),
      (∀ m, d.graph m = (hsys α β (.mu b) (π.symm m)).bind fun j => .leaf (π j)) ∧
      d.sol Mean.d (π ⟨0, Nat.succ_pos _⟩) = denote α β (.mu b) [] := by
  obtain ⟨π, d, hrel, h3, _⟩ := hoist_solution α β (.mu b) hg
  exact ⟨π, d, hrel, h3 _⟩

end THoistOrder

/-! ## A closed binder below a wall hoists, with its meaning

The guard admits a closed binder below `legacy` or `held`. A stratified system has no form for a
leaf below a wall (`wall_leaf_no_strat`). The DAG of scopes puts the inner binder in a later
scope, and the wall names it as a constant. -/

section WallTerms
variable {S : Syn} [Sem S] (α : Table S) (β : Table S.op)

/-- A closed binder below `legacy`, inside a binder: the guard admits it. -/
abbrev wallLegacy (r : S.sig.R) : Term S.sig := .mu (.list [.legacy (.mu (.list [.var 0] none [])) r] none [])

/-- A closed binder below `held`: the guard admits it. -/
abbrev wallHeld (k₀ : S.sig.G true × Bool) : Term S.sig := .held true (.mu (.list [.var 0] none [])) .opaq k₀ []

example (r : S.sig.R) : (wallLegacy r).guarded = true := rfl
example (k₀ : S.sig.G true × Bool) : (wallHeld k₀).guarded = true := rfl

/-- Below `legacy`: the entry of the outer binder in the solution is its denotation. -/
theorem wallLegacy_hoist (r : S.sig.R) :
    ∃ (π : Equiv.Perm (Fin (muC (wallLegacy r)))) (d : DSys (HS S) (muC (wallLegacy r))),
      (∀ m, d.graph m = (hsys α β (wallLegacy r) (π.symm m)).bind fun j => .leaf (π j)) ∧
      d.sol Mean.d (π ⟨0, Nat.succ_pos _⟩) = denote α β (wallLegacy r) [] :=
  hoist_mu α β (.list [.legacy (.mu (.list [.var 0] none [])) r] none []) rfl

/-- Below `held`: the term over the solution is its denotation, and the entry of the inner
    binder is the denotation of the inner binder. -/
theorem wallHeld_hoist (k₀ : S.sig.G true × Bool) :
    ∃ (π : Equiv.Perm (Fin (muC (wallHeld k₀)))) (d : DSys (HS S) (muC (wallHeld k₀))),
      d.sol Mean.d (π ⟨0, by simp [muC, muCL, muCO]⟩) = denote α β (.mu (.list [.var 0] none [])) [] ∧
      (hoist α β (wallHeld k₀) (fun m => π m) noEnv).interp (HS S) (d.sol Mean.d) =
        denote α β (wallHeld k₀) [] := by
  obtain ⟨π, d, _, h3, h4⟩ := hoist_solution α β (wallHeld k₀) rfl
  refine ⟨π, d, (h3 ⟨0, by simp [muC, muCL, muCO]⟩).trans ?_, h4⟩
  exact Fin.append_left (vals α β (.mu (.list [.var 0] none [])) []) (vals α β .opaq [])
    ⟨0, Nat.succ_pos _⟩

/-- The legacy term's hoisted system: two entries, and a wall edge from the outer binder to the
    inner one. The inner binder sits in a later scope than the outer binder reads it from. -/
example (r : S.sig.R) : (hsys α β (wallLegacy r) ⟨0, by simp [muC, muCL, muCO]⟩).wlv (HS S) ⟨1, by simp [muC, muCL, muCO]⟩ = true := rfl

/-- An object with a binder below it, and a binder below a slot: the hoist covers `object`. -/
abbrev objTerm : Term S.sig :=
  .mu (.object (.mk {"a", "b"} (fun k => if k.1 = "a" then .optional (.var 0)
    else .req (.mu (.list [.var 0, .var 1] none []))) none))

example : (objTerm (S := S)).guarded = true := rfl

/-- At an object: the entry of the binder in the solution is its denotation. -/
theorem objTerm_hoist :
    ∃ (π : Equiv.Perm (Fin (muC (objTerm (S := S))))) (d : DSys (HS S) (muC (objTerm (S := S)))),
      (∀ m, d.graph m = (hsys α β objTerm (π.symm m)).bind fun j => .leaf (π j)) ∧
      d.sol Mean.d (π ⟨0, Nat.succ_pos _⟩) = denote α β objTerm [] :=
  hoist_mu α β _ rfl

example : muC (objTerm (S := S)) = 2 := rfl

end WallTerms

section WallCycle

/-- The guard refuses a recursion through a wall: `X = held(X)`. -/
example {S : Syn} [Sem S] (k₀ : S.sig.G true × Bool) :
    (Term.mu (.held true (.var 0) .opaq k₀ []) : Term S.sig).guarded = false := rfl

end WallCycle

/-! ## `Compat` at a union below a binder -/

section CompatNested
variable {S : Syn} [Sem S] (α : Table S) (β : Table S.op)



/-- **Compatibility by approximation of the environment**: if, at every depth, an environment that
    each variable's level lets agree with `ρ` makes the options pairwise compatible, so does `ρ`. -/
theorem compat_env_approx (opts : List (Term S.sig)) (hg : Term.guardedL opts = true)
    (ρ : List S.C)
    (h : ∀ k, ∃ ρ', PairwiseCompat α β opts ρ' ∧
      ∀ s ∈ opts, ∀ i, UseAgree (s.use i) k (envAt ρ i) (envAt ρ' i)) :
    PairwiseCompat α β opts ρ := fun s hs t ht =>
  compat_of_approx (depth := Mean.d) fun k => by
    obtain ⟨ρ', hC, hA⟩ := h k
    exact ⟨_, _, denote_agree s (guardedL_mem hg hs) k ρ ρ' (hA s hs),
      denote_agree t (guardedL_mem hg ht) k ρ ρ' (hA t ht), hC s hs t ht⟩

/-- **A union below two binders**: the obligations give `PairwiseCompat` at the stages of both
    binders. The guard carries it to the limit of both, which is the environment of the union:
    the codec of the inner binder, then the codec of the outer binder. -/
theorem compat_nested (opts : List (Term S.sig))
    (hg : (Term.mu (.mu (.union opts))).guarded = true)
    (hob : Obligations α β (.mu (.mu (.union opts))) [])
    (hs₁ : ∀ n, Lawful Mean.mem (muStage (fun c => denote α β (.mu (.union opts)) [c]) n))
    (hs₂ : ∀ n m, Lawful Mean.mem (muStage (fun c => denote α β (.union opts)
      [c, muStage (fun c => denote α β (.mu (.union opts)) [c]) n]) m)) :
    PairwiseCompat α β opts [denote α β (.mu (.union opts)) [denote α β (.mu (.mu (.union opts))) []],
      denote α β (.mu (.mu (.union opts))) []] := by
  have hg' := hg
  simp only [Term.guarded, Bool.and_eq_true, decide_eq_true_eq] at hg'
  obtain ⟨hout, hin, hopts⟩ := hg'
  have hgin : (Term.mu (.union opts)).guarded = true := by
    simp only [Term.guarded, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hin, hopts⟩
  let O := denote α β (.mu (.mu (.union opts))) []
  let Ok : Nat → S.C := muStage fun c => denote α β (.mu (.union opts)) [c]
  let Ik : Nat → S.C := fun k => muStage (fun c => denote α β (.union opts) [c, Ok k]) k
  have hO : ∀ k, AgreeLe Mean.d k O (Ok k) := fun k => muCodec_agree Mean.d_pos (contractive_body hg []) k
  have hI : ∀ k, AgreeLe Mean.d k (denote α β (.mu (.union opts)) [O]) (Ik k) := fun k =>
    (denote_agree (.mu (.union opts)) hgin k [O] [Ok k] fun i => match i with
      | 0 => UseAgree.mono (u' := 2) (hO k) (le_trans hout (by omega))
      | _ + 1 => UseAgree.refl _ _ _).trans
      (muCodec_agree Mean.d_pos (contractive_body hgin [Ok k]) k)
  refine compat_env_approx α β opts hopts _ fun k => ⟨[Ik k, Ok k], ?_, fun s hs i => ?_⟩
  · exact ((hob k (hs₁ k)) k (hs₂ k k)).2
  · match i with
    | 0 => exact UseAgree.mono (u' := 2) (hI k) (le_trans (useL_mem 0 hs) (le_trans hin (by omega)))
    | 1 => exact UseAgree.mono (u' := 2) (hO k) (le_trans (useL_mem 1 hs) (le_trans hout (by omega)))
    | _ + 2 => exact UseAgree.refl _ _ _

/-- **`Compat` at the solution**: the options of the union are pairwise compatible at the
    solution of the DAG of scopes: the entry of the inner binder, then the entry of the outer
    binder. -/
theorem compat_nested_sol (opts : List (Term S.sig))
    (hg : (Term.mu (.mu (.union opts))).guarded = true)
    (hob : Obligations α β (.mu (.mu (.union opts))) [])
    (hs₁ : ∀ n, Lawful Mean.mem (muStage (fun c => denote α β (.mu (.union opts)) [c]) n))
    (hs₂ : ∀ n m, Lawful Mean.mem (muStage (fun c => denote α β (.union opts)
      [c, muStage (fun c => denote α β (.mu (.union opts)) [c]) n]) m)) :
    ∃ (π : Equiv.Perm (Fin (muC (Term.mu (.mu (.union opts))))))
      (d : DSys (HS S) (muC (Term.mu (.mu (.union opts))))),
      (∀ m, d.graph m = (hsys α β (.mu (.mu (.union opts))) (π.symm m)).bind fun j => .leaf (π j)) ∧
      PairwiseCompat α β opts [d.sol Mean.d (π ⟨1, Nat.succ_lt_succ (Nat.succ_pos _)⟩), d.sol Mean.d (π ⟨0, Nat.succ_pos _⟩)] := by
  obtain ⟨π, d, hrel, h3, _⟩ := hoist_solution α β (.mu (.mu (.union opts))) hg
  refine ⟨π, d, hrel, ?_⟩
  rw [h3, h3]
  exact compat_nested α β opts hg hob hs₁ hs₂

end CompatNested

section CompatTerm
variable {S : Syn} [Sem S] (α : Table S) (β : Table S.op)

/-- **A union below one binder**: the obligations give `PairwiseCompat` at each lawful stage. The
    guard carries it to the limit, which is the denotation of the binder. -/
theorem compat_mu_union (opts : List (Term S.sig)) (hg : (Term.mu (.union opts)).guarded = true)
    (hob : Obligations α β (.mu (.union opts)) [])
    (hs : ∀ n, Lawful Mean.mem (muStage (fun c => denote α β (.union opts) [c]) n)) :
    PairwiseCompat α β opts [denote α β (.mu (.union opts)) []] := by
  have hg' := hg
  simp only [Term.guarded, Bool.and_eq_true, decide_eq_true_eq] at hg'
  have hB := contractive_body (α := α) (β := β) hg []
  intro s hs' t ht'
  have hst : ∀ k, PairwiseCompat α β opts [muStage (fun c => denote α β (.union opts) [c]) k] :=
    fun k => (hob k (hs k)).2
  have hag : ∀ u ∈ opts, ∀ k, AgreeLe Mean.d k (denote α β u [denote α β (.mu (.union opts)) []])
      (denote α β u [muStage (fun c => denote α β (.union opts) [c]) k]) := fun u hu k =>
    denote_agree u (guardedL_mem hg'.2 hu) k _ _ fun i => match i with
      | 0 => UseAgree.mono (u' := 2) (muCodec_agree Mean.d_pos hB k)
          (le_trans (useL_mem 0 hu) (le_trans hg'.1 (by omega)))
      | _ + 1 => UseAgree.refl _ _ _
  exact compat_of_approx (depth := Mean.d) fun k =>
    ⟨_, _, hag s hs' k, hag t ht' k, hst k s hs' t ht'⟩

end CompatTerm

section LawfulHoist
variable {S : Syn} [Sem S] (α : Table S) (β : Table S.op)

/-- **Lawfulness at the solution**: under the hypotheses of `lawful_muCodec`, the entry of a closed
    binder in the solution is lawful. -/
theorem hoist_lawful (b : Term S.sig) (hg : (Term.mu b).guarded = true)
    (hs : ∀ n, Lawful Mean.mem (muStage (fun c => denote α β b [c]) n)) :
    ∃ (π : Equiv.Perm (Fin (muC (Term.mu b)))) (d : DSys (HS S) (muC (Term.mu b))),
      (∀ m, d.graph m = (hsys α β (.mu b) (π.symm m)).bind fun j => .leaf (π j)) ∧
      Lawful Mean.mem (d.sol Mean.d (π ⟨0, Nat.succ_pos _⟩)) := by
  obtain ⟨π, d, hrel, h0⟩ := hoist_mu α β b hg
  exact ⟨π, d, hrel, h0 ▸ lawful_muCodec Mean.d_pos (contractive_body hg []) hs⟩

end LawfulHoist

end Calculus.Alg
