import Calculus.Alg.Recursion
import Mathlib.Data.PFunctor.Univariate.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Systems of recursive codecs, over any carriers

A system has `n` entries. Each entry is a body that reads every entry. The solution reads each
input at the stage that the depth of the input names, as `muCodec` does. The guard is
`ContractiveV`: agreement below `d` at every entry gives agreement below `d + 1`. Under the guard
the solution is the one fixed point at the maps, and lawful stages give a lawful solution.

The syntactic layer is a flat term over one constructor step: `Flat`, a free monad with one leaf
for each entry. Each operation of the step has a kind. A `keep` reads its arguments at the depth
of the input, a `down` reads them one layer down, and a `wall` reads them at any depth. The join
`altCodec` and the restriction `Codec.restrict` are `keep` operations, and the join laws hold
as equalities.

A system that has no leaf under a wall and no cycle of unguarded edges has one solution: the
ε-elimination substitutes the system into its own leaves, and after `n` rounds each entry is
guarded. `graphGuard` decides the condition. The stratified form `SSys` names a leaf above every
guard only below its own entry, so the condition holds by construction, and `nf` folds the
system into a guarded one. The graph form of a stratified system passes `graphGuard`.

A wall can read an entry that the wall cannot reach back. The DAG of scopes `DSys` is a sequence
of stratified scopes, and a scope reads each earlier entry as a constant. `DagGuard` admits a
wall edge that leaves its component. The graph form of a DAG of scopes passes `DagGuard` under
each renaming of its entries, and each DAG of scopes has one solution at the maps.
-/

namespace Calculus.Alg

variable {V M : Type} {member : V → M} (depth : V → Nat) {n : Nat}

/-- Agreement below `d` at every entry. -/
def AgreeLeV (d : Nat) (e₁ e₂ : Fin n → Codec V M) : Prop := ∀ i, AgreeLe depth d (e₁ i) (e₂ i)

/-- The vector guard: agreement below `d` at every entry gives agreement below `d + 1` at every
    entry. -/
def ContractiveV (B : (Fin n → Codec V M) → Fin n → Codec V M) : Prop :=
  ∀ d e₁ e₂, AgreeLeV depth d e₁ e₂ → AgreeLeV depth (d + 1) (B e₁) (B e₂)

/-- The stages, by structural recursion on the depth. -/
def sysStage (B : (Fin n → Codec V M) → Fin n → Codec V M) : Nat → Fin n → Codec V M
  | 0 => fun _ => .empty
  | k + 1 => B (sysStage B k)

/-- The solution: each entry reads each input at the stage that the input's depth names. -/
def solve (B : (Fin n → Codec V M) → Fin n → Codec V M) (i : Fin n) : Codec V M where
  T v := ((sysStage B (depth v) i).e v).isSome = true
  μ := none
  f o x := (sysStage B (depth x) i).f o x

variable {depth}

section Laws
variable (hd : ∀ v, 0 < depth v) {B : (Fin n → Codec V M) → Fin n → Codec V M}
include hd

/-- Under the guard, stage `k` and stage `k + 1` agree below `k` at every entry. -/
theorem sysStage_stable (hB : ContractiveV depth B) :
    ∀ k, AgreeLeV depth k (sysStage B k) (sysStage B (k + 1))
  | 0 => fun _ => AgreeLe.zero hd _ _
  | k + 1 => hB k _ _ (sysStage_stable hB k)

/-- Under the guard, stage `d` and each later stage agree below `d` at every entry. -/
theorem sysStage_agree (hB : ContractiveV depth B) {d : Nat} :
    ∀ k, AgreeLeV depth d (sysStage B d) (sysStage B (d + k))
  | 0 => fun _ => AgreeLe.refl _ _
  | k + 1 => fun i =>
      (sysStage_agree hB k i).trans ((sysStage_stable hd hB (d + k) i).mono (by omega))

/-- Under the guard, stage `d` and stage `m ≥ d` agree below `d` at every entry. -/
theorem sysStage_agree_le (hB : ContractiveV depth B) {d m : Nat} (h : d ≤ m) :
    AgreeLeV depth d (sysStage B d) (sysStage B m) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact sysStage_agree hd hB k

/-- Under the guard, the solution and stage `k` agree below `k` at every entry. -/
theorem solve_agree (hB : ContractiveV depth B) (k : Nat) :
    AgreeLeV depth k (solve depth B) (sysStage B k) :=
  fun i => ⟨fun o x hx => (sysStage_agree_le hd hB hx i).f o x le_rfl⟩

/-- **The fixpoint law.** Each entry of the solution is its body at the solution. -/
theorem solve_fix (hB : ContractiveV depth B) (i : Fin n) (o : Orient) (x : V) :
    (solve depth B i).f o x = (B (solve depth B) i).f o x := by
  obtain ⟨k, hk⟩ : ∃ k, depth x = k + 1 := ⟨depth x - 1, by have := hd x; omega⟩
  show (sysStage B (depth x) i).f o x = _
  rw [hk]
  exact (hB k _ _ (fun j => (solve_agree hd hB k j).symm) i).f o x (by omega)

/-- **Uniqueness.** Any vector that satisfies the fixpoint law agrees with the solution at every
    depth. -/
theorem solve_unique (hB : ContractiveV depth B) {e : Fin n → Codec V M}
    (he : ∀ i o x, (e i).f o x = (B e i).f o x) : ∀ d, AgreeLeV depth d e (solve depth B) := by
  intro d
  induction d with
  | zero => exact fun _ => AgreeLe.zero hd _ _
  | succ d ih =>
    intro i
    refine ⟨fun o x hx => ?_⟩
    rw [he i o x, solve_fix hd hB i o x]
    exact (hB d _ _ ih i).f o x hx

/-- **Lawfulness**: lawful stages give a lawful solution, at each entry. -/
theorem lawful_solve (hB : ContractiveV depth B)
    (hs : ∀ k i, Lawful member (sysStage B k i)) (i : Fin n) : Lawful member (solve depth B i) :=
  lawful_of_approx fun d => ⟨_, hs d i, solve_agree hd hB d i, fun _ h => nomatch h⟩

end Laws

/-! ## The guard is necessary: refutations on the carrier `Nat`, with depth `v + 1` -/

section Concrete

/-- The depth of the concrete carrier. -/
abbrev dN : Nat → Nat := fun v => v + 1

/-- A codec that sends every input to itself. -/
def idc : Codec Nat Unit := { T := fun _ => True, μ := none, f := fun _ x => some x }

/-- **Uniqueness needs the guard**: the identity body has every vector as a fixed point. -/
theorem unique_fails_id :
    ¬ ∀ e : Fin 1 → Codec Nat Unit, (∀ i o x, (e i).f o x = ((fun e => e) e i).f o x) →
      ∀ d, AgreeLeV dN d e (solve dN (fun e => e)) := by
  intro h
  have := (h (fun _ => idc) (fun _ _ _ => rfl) 1 0).f Orient.host 0 (by decide)
  have hs : ∀ k, sysStage (n := 1) (V := Nat) (M := Unit) (fun e => e) k 0 = .empty := by
    intro k; induction k with
    | zero => rfl
    | succ k ih => exact ih
  simp only [solve, idc, hs, Codec.empty] at this
  cases this

/-- The system where each entry is the other entry. -/
def swapB : (Fin 2 → Codec Nat Unit) → Fin 2 → Codec Nat Unit := fun e i => e (Fin.rev i)

/-- The swap system is not contractive. -/
theorem swap_not_contractive : ¬ ContractiveV dN swapB := by
  intro h
  have := (h 0 (fun _ => idc) (fun _ => .empty) (fun _ => ⟨fun _ x hx => by
    simp [dN] at hx⟩) 0).f Orient.host 0 (by decide)
  simp [swapB, idc, Codec.empty] at this

/-- The swap system has a fixed point that the solution does not agree with. -/
theorem swap_unique_fails :
    ¬ ∀ e : Fin 2 → Codec Nat Unit, (∀ i o x, (e i).f o x = (swapB e i).f o x) →
      ∀ d, AgreeLeV dN d e (solve dN swapB) := by
  intro h
  have := (h (fun _ => idc) (fun _ _ _ => rfl) 1 0).f Orient.host 0 (by decide)
  have hs : ∀ k i, sysStage swapB k i = .empty := by
    intro k; induction k with
    | zero => intro _; rfl
    | succ k ih => intro i; exact ih _
  simp only [solve, idc, hs, Codec.empty] at this
  cases this

/-- A body that reads its argument one layer down: `0` maps to itself, `x + 1` reads `x`. -/
def shift (c : Codec Nat Unit) : Codec Nat Unit :=
  { T := fun _ => True, μ := none, f := fun o x => match x with | 0 => some 0 | x + 1 => c.f o x }

/-- Entry 0 is `shift` of entry 1, and entry 1 is entry 0. The cycle has a guard, but entry 1
    reads entry 0 at its own depth, so the system is not `ContractiveV`. -/
def triB : (Fin 2 → Codec Nat Unit) → Fin 2 → Codec Nat Unit :=
  fun e i => match i with
    | ⟨0, _⟩ => shift (e 1)
    | ⟨_ + 1, _⟩ => e 0

/-- **`solve` needs `ContractiveV`, not a guarded cycle**: on `triB`, the solution breaks the
    fixpoint law. The ε-elimination solves this shape. -/
theorem tri_solve_not_fix :
    (solve dN triB 1).f Orient.host 0 ≠ (triB (solve dN triB) 1).f Orient.host 0 := by
  decide

end Concrete

/-! ## The syntactic layer: a free monad over one constructor step, with `Fin n` leaves. -/

/-- How an operation reads the depth: at the input's depth, one layer down, or at any depth. -/
inductive Kind | keep | down | wall

/-- **The signature of a step**: a polynomial functor (the operations `A` and the positions `B` of
    each), a structural enumeration of the positions, and the kind of each operation. It holds no
    meaning. -/
structure Container extends PFunctor.{0, 0} where
  /-- The positions of each operation, enumerated by a structural list. -/
  pos : (o : A) → List (B o)
  pos_complete : ∀ o (p : B o), p ∈ pos o
  kind : A → Kind

/-- The operations of a signature. -/
abbrev Container.Op (S : Container) : Type := S.A

/-- The positions of an operation. -/
abbrev Container.Pos (S : Container) : S.Op → Type := S.B

/-- **An algebra over a signature**: the codec of each operation from the codecs of its positions. -/
structure Step (S : Container) (V M : Type) where
  run : (o : S.Op) → (S.Pos o → Codec V M) → Codec V M

/-- What the step owes: `keep` keeps agreement, `down` adds one layer. `wall` owes nothing. -/
structure Step.Lawful {S : Container} (depth : V → Nat) (R : Step S V M) : Prop where
  keep : ∀ o, S.kind o = .keep → ∀ d (a₁ a₂ : S.Pos o → Codec V M),
    (∀ p, AgreeLe depth d (a₁ p) (a₂ p)) → AgreeLe depth d (R.run o a₁) (R.run o a₂)
  down : ∀ o, S.kind o = .down → ∀ d (a₁ a₂ : S.Pos o → Codec V M),
    (∀ p, AgreeLe depth d (a₁ p) (a₂ p)) → AgreeLe depth (d + 1) (R.run o a₁) (R.run o a₂)

/-- The free monad over the step, with a leaf for each entry. -/
inductive Flat (Op : Type) (Pos : Op → Type) (n : Nat) where
  | leaf (i : Fin n)
  | node (o : Op) (args : Pos o → Flat Op Pos n)

variable {S : Container} {R : Step S V M}

/-- The codec of a flat term over an environment of entries. -/
def Flat.interp (R : Step S V M) (e : Fin n → Codec V M) : Flat S.Op S.Pos n → Codec V M
  | .leaf i => e i
  | .node o args => R.run o fun p => Flat.interp R e (args p)

/-- No leaf. -/
def Flat.Closed (S : Container) : Flat S.Op S.Pos n → Prop
  | .leaf _ => False
  | .node _ args => ∀ p, Flat.Closed S (args p)

/-- No leaf under a `wall`. -/
def Flat.Ok (S : Container) : Flat S.Op S.Pos n → Prop
  | .leaf _ => True
  | .node o args => match S.kind o with
    | .wall => ∀ p, Flat.Closed S (args p)
    | _ => ∀ p, Flat.Ok S (args p)

/-- The guard: each leaf under a `down`, and no leaf under a `wall`. -/
def Flat.Guarded (S : Container) : Flat S.Op S.Pos n → Prop
  | .leaf _ => False
  | .node o args => match S.kind o with
    | .keep => ∀ p, Flat.Guarded S (args p)
    | .down => ∀ p, Flat.Ok S (args p)
    | .wall => ∀ p, Flat.Closed S (args p)

/-- A flat term with no leaf has one codec over every environment. -/
theorem Flat.interp_closed (e₁ e₂ : Fin n → Codec V M) :
    ∀ t : Flat S.Op S.Pos n, t.Closed S → t.interp R e₁ = t.interp R e₂
  | .leaf _, h => h.elim
  | .node o args, h => by
      simp only [Flat.interp]
      exact congrArg (R.run o) (funext fun p => Flat.interp_closed e₁ e₂ (args p) (h p))

/-- A flat term with no leaf under a wall keeps agreement below `d` of its environments. -/
theorem Flat.ok_agree (hS : R.Lawful depth) {d : Nat} {e₁ e₂ : Fin n → Codec V M}
    (he : AgreeLeV depth d e₁ e₂) :
    ∀ t : Flat S.Op S.Pos n, t.Ok S → AgreeLe depth d (t.interp R e₁) (t.interp R e₂)
  | .leaf i, _ => he i
  | .node o args, h => by
      simp only [Flat.Ok] at h
      simp only [Flat.interp]
      cases hk : S.kind o with
      | keep =>
        rw [hk] at h
        exact hS.keep o hk d _ _ fun p => Flat.ok_agree hS he (args p) (h p)
      | down =>
        rw [hk] at h
        exact (hS.down o hk d _ _ fun p => Flat.ok_agree hS he (args p) (h p)).mono (by omega)
      | wall =>
        rw [hk] at h
        rw [congrArg (R.run o) (funext fun p => Flat.interp_closed e₁ e₂ (args p) (h p))]
        exact AgreeLe.refl _ _

/-- A guarded flat term turns agreement below `d` of its environments into agreement below
    `d + 1`. -/
theorem Flat.guarded_agree (hS : R.Lawful depth) {d : Nat} {e₁ e₂ : Fin n → Codec V M}
    (he : AgreeLeV depth d e₁ e₂) :
    ∀ t : Flat S.Op S.Pos n, t.Guarded S → AgreeLe depth (d + 1) (t.interp R e₁) (t.interp R e₂)
  | .leaf _, h => h.elim
  | .node o args, h => by
      simp only [Flat.Guarded] at h
      simp only [Flat.interp]
      cases hk : S.kind o with
      | keep =>
        rw [hk] at h
        exact hS.keep o hk (d + 1) _ _ fun p => Flat.guarded_agree hS he (args p) (h p)
      | down =>
        rw [hk] at h
        exact hS.down o hk d _ _ fun p => Flat.ok_agree hS he (args p) (h p)
      | wall =>
        rw [hk] at h
        rw [congrArg (R.run o) (funext fun p => Flat.interp_closed e₁ e₂ (args p) (h p))]
        exact AgreeLe.refl _ _

/-- **A guarded system's interpretation is contractive.** -/
theorem contractive_of_guarded (hS : R.Lawful depth) (sys : Fin n → Flat S.Op S.Pos n)
    (hg : ∀ i, (sys i).Guarded S) : ContractiveV depth fun e i => (sys i).interp R e :=
  fun _ _ _ he i => Flat.guarded_agree hS he (sys i) (hg i)

/-- The guard refuses the system where each entry is the other entry. -/
theorem swap_refused (S : Container) :
    ¬ ∀ i, ((fun i => .leaf (Fin.rev i)) : Fin 2 → Flat S.Op S.Pos 2) i |>.Guarded S :=
  fun h => h 0

/-! ## `muCodec` is a system of one entry -/

section OneEntry
variable {V M : Type} {depth : V → Nat}

/-- The stages of a one-entry system are the stages of its body. -/
theorem sysStage_one (F : Codec V M → Codec V M) :
    ∀ k, sysStage (fun env (_ : Fin 1) => F (env 0)) k 0 = muStage F k
  | 0 => rfl
  | k + 1 => by
      show F (sysStage _ k 0) = F (muStage F k)
      rw [sysStage_one F k]

/-- A codec whose held set is its write domain and whose member is `⊤` is fixed by its map. -/
theorem solve_eq {n : Nat} {B : (Fin n → Codec V M) → Fin n → Codec V M} {i : Fin n}
    {c : Codec V M} (hT : ∀ v, c.T v = ((c.e v).isSome = true)) (hμ : c.μ = none)
    (hf : (solve depth B i).f = c.f) : solve depth B i = c := by
  obtain ⟨T, μ, f⟩ := c
  simp only at hT hμ hf
  subst hμ
  have hT' : T = fun v => ((f Orient.host v).isSome = true) := funext hT
  subst hT' hf
  rfl

/-- **`muCodec` is entry 0 of the one-entry system**, with no hypothesis. -/
theorem solve_one (F : Codec V M → Codec V M) :
    solve depth (fun env (_ : Fin 1) => F (env 0)) 0 = muCodec depth F :=
  solve_eq (fun _ => rfl) rfl (funext fun o => funext fun x => by
    show (sysStage _ (depth x) 0).f o x = (muStage F (depth x)).f o x
    rw [sysStage_one])

/-! ## Bekić for a pair: a `muCodec` inside a `muCodec` is a two-entry system. -/

/-- The two-entry system `X = F X Y`, `Y = G X Y`. -/
def pairB (F G : Codec V M → Codec V M → Codec V M) :
    (Fin 2 → Codec V M) → Fin 2 → Codec V M :=
  fun e i => match i with
    | ⟨0, _⟩ => F (e 0) (e 1)
    | ⟨_ + 1, _⟩ => G (e 0) (e 1)

/-- Contractive in both arguments. -/
def Contractive2 (depth : V → Nat) (F : Codec V M → Codec V M → Codec V M) : Prop :=
  ∀ d x₁ x₂ y₁ y₂, AgreeLe depth d x₁ x₂ → AgreeLe depth d y₁ y₂ →
    AgreeLe depth (d + 1) (F x₁ y₁) (F x₂ y₂)

/-- Two bodies that are contractive in both arguments give a contractive pair system. -/
theorem pairB_contractive {F G : Codec V M → Codec V M → Codec V M}
    (hF : Contractive2 depth F) (hG : Contractive2 depth G) : ContractiveV depth (pairB F G) :=
  fun d _ _ he i => match i with
    | ⟨0, _⟩ => hF d _ _ _ _ (he 0) (he 1)
    | ⟨1, _⟩ => hG d _ _ _ _ (he 0) (he 1)

/-- **Bekić.** Entry 0 of the pair system is the nested `muCodec`, and entry 1 is the inner
    `muCodec` at entry 0. -/
theorem bekic (hd : ∀ v, 0 < depth v) {F G : Codec V M → Codec V M → Codec V M}
    (hF : Contractive2 depth F) (hG : Contractive2 depth G) :
    solve depth (pairB F G) 0 = muCodec depth (fun x => F x (muCodec depth (G x))) ∧
    solve depth (pairB F G) 1 =
      muCodec depth (G (muCodec depth (fun x => F x (muCodec depth (G x))))) := by
  have hA : Contractive depth (fun x => F x (muCodec depth (G x))) := fun d x₁ x₂ hx =>
    hF d _ _ _ _ hx (agreeLe_muCodec fun c₁ c₂ hc => (hG d _ _ _ _ hx hc).mono (by omega))
  have hGA : ∀ x, Contractive depth (G x) := fun x d c₁ c₂ hc =>
    hG d _ _ _ _ (AgreeLe.refl _ _) hc
  let A := muCodec depth (fun x => F x (muCodec depth (G x)))
  let e : Fin 2 → Codec V M := fun i => match i with
    | ⟨0, _⟩ => A
    | ⟨_ + 1, _⟩ => muCodec depth (G A)
  have he : ∀ i o x, (e i).f o x = (pairB F G e i).f o x := fun i o x => match i with
    | ⟨0, _⟩ => muCodec_fix hd hA o x
    | ⟨1, _⟩ => muCodec_fix hd (hGA A) o x
  have hu := solve_unique hd (pairB_contractive hF hG) he
  have hf : ∀ i, (solve depth (pairB F G) i).f = (e i).f := fun i =>
    AgreeLe.eq_of_forall fun d => (hu d i).symm
  exact ⟨solve_eq (fun _ => rfl) rfl (hf 0), solve_eq (fun _ => rfl) rfl (hf 1)⟩

end OneEntry

/-! ## The join laws -/

section Join

/-- The join is commutative over lawful, pairwise compatible options. -/
theorem join_comm {os os' : List (Codec V M)} (h : os.Perm os') (μ : Option M)
    (hl : ∀ o ∈ os, Lawful member o) (hC : ∀ o ∈ os, ∀ o' ∈ os, Compat o o') :
    altCodec os μ = altCodec os' μ :=
  altCodec_perm h μ hl hC

/-- The first answer of an appended list is the first answer of the head, else of the tail. -/
theorem select_append {X Y : Type} (run : Codec V M → X → Option Y) (x : X) :
    ∀ os rest : List (Codec V M),
      select (os ++ rest) run x = (select os run x).or (select rest run x)
  | [], _ => rfl
  | o :: os, rest => by
      rw [List.cons_append, select_cons, select_cons, select_append run x os rest]
      cases run o x <;> simp

/-- A list gives no answer exactly where each member gives no answer. -/
theorem select_eq_none {X Y : Type} (run : Codec V M → X → Option Y) (x : X) :
    ∀ os : List (Codec V M), select os run x = none ↔ ∀ c ∈ os, run c x = none
  | [] => by simp [select_nil_eq]
  | o :: os => by
      rw [select_cons]
      cases h : run o x <;> simp [h, select_eq_none run x os]

/-- The first answer of `o :: os` is the answer of `o`, else the first answer of `os`. -/
theorem select_cons_or {X Y : Type} (o : Codec V M) (os : List (Codec V M))
    (run : Codec V M → X → Option Y) (x : X) :
    select (o :: os) run x = (run o x).or (select os run x) := by
  rw [select_cons]; cases run o x <;> rfl

/-- The map of the join is the first answer of its options. -/
theorem altCodec_f_eq (ps : List (Codec V M)) (μ : Option M) (o : Orient) (x : V) :
    (altCodec ps μ).f o x = select ps (·.f o) x := rfl

/-- **The join is idempotent**: a repeated option changes nothing. No hypothesis. -/
theorem join_dup {a : Codec V M} {os : List (Codec V M)} (ha : a ∈ os) (qs : List (Codec V M))
    (μ : Option M) : altCodec (os ++ a :: qs) μ = altCodec (os ++ qs) μ := by
  have hf : ∀ o : Orient, (altCodec (os ++ a :: qs) μ).f o = (altCodec (os ++ qs) μ).f o := by
    intro o; funext x
    rw [altCodec_f_eq, altCodec_f_eq, select_append, select_append, select_cons]
    cases h : select os (·.f o) x with
    | some y => rfl
    | none =>
      have hn : a.f o x = none := (select_eq_none _ x os).mp h a ha
      simp [hn]
  refine Codec.ext ?_ rfl (hf .host) (hf .dual)
  funext v
  apply propext
  simp only [altCodec, List.mem_append, List.mem_cons]
  constructor
  · rintro ⟨c, hc | rfl | hc, hT⟩
    · exact ⟨c, Or.inl hc, hT⟩
    · exact ⟨_, Or.inl ha, hT⟩
    · exact ⟨c, Or.inr hc, hT⟩
  · rintro ⟨c, hc | hc, hT⟩
    · exact ⟨c, Or.inl hc, hT⟩
    · exact ⟨c, Or.inr (Or.inr hc), hT⟩

/-- The join of two copies of an option is the join of one copy. -/
theorem join_idem (a : Codec V M) (μ : Option M) : altCodec [a, a] μ = altCodec [a] μ :=
  join_dup (os := [a]) (List.mem_singleton_self a) [] μ

/-- **The join is flat**: an inner join at any position is its options at that position. No
    hypothesis. The member of the inner join drops out. -/
theorem join_flat (os ps qs : List (Codec V M)) (μ μ' : Option M) :
    altCodec (os ++ altCodec ps μ' :: qs) μ = altCodec (os ++ ps ++ qs) μ := by
  have hf : ∀ o : Orient,
      (altCodec (os ++ altCodec ps μ' :: qs) μ).f o = (altCodec (os ++ ps ++ qs) μ).f o := by
    intro o; funext x
    simp only [altCodec_f_eq, select_append, select_cons_or]
    cases select os (·.f o) x <;> cases select ps (·.f o) x <;> rfl
  refine Codec.ext ?_ rfl (hf .host) (hf .dual)
  funext v
  apply propext
  simp only [altCodec, List.mem_append, List.mem_cons]
  constructor
  · rintro ⟨c, hc | rfl | hc, hT⟩
    · exact ⟨c, Or.inl (Or.inl hc), hT⟩
    · obtain ⟨d, hd, hT'⟩ := hT
      exact ⟨d, Or.inl (Or.inr hd), hT'⟩
    · exact ⟨c, Or.inr hc, hT⟩
  · rintro ⟨c, (hc | hc) | hc, hT⟩
    · exact ⟨c, Or.inl hc, hT⟩
    · exact ⟨_, Or.inr (Or.inl rfl), c, hc, hT⟩
    · exact ⟨c, Or.inr (Or.inr hc), hT⟩

/-! ## The join and the restriction add no depth

`agreeLe_altCodec` and `agreeLe_refine2` are the `keep` law of the join and of the two-sided
restriction. The restriction is one instance. -/

/-- A restriction keeps agreement below `d`. -/
theorem agreeLe_restrict {d : Nat} {c₁ c₂ : Codec V M} (h : AgreeLe depth d c₁ c₂) (q : V → Bool) :
    AgreeLe depth d (c₁.restrict q) (c₂.restrict q) :=
  agreeLe_refine2 h q _

/-! ## The restriction distributes over the join -/

/-- The host map of a restriction answers where the predicate holds, and nowhere else. -/
theorem restrict_host (c : Codec V M) (q : V → Bool) (v : V) :
    (c.restrict q).f Orient.host v = if q v then c.f Orient.host v else none := by
  simp only [Codec.restrict, refine2, Side.elim, Orient.host]
  cases q v <;> simp

/-- The dual map of a restriction keeps an answer where the predicate holds on the answer. -/
theorem restrict_dual (c : Codec V M) (q : V → Bool) (a : V) :
    (c.restrict q).f Orient.dual a = (c.f Orient.dual a).bind fun y => if q y then some y else none := by
  simp only [Codec.restrict, refine2, Side.elim, Orient.dual]
  simp
  rfl

/-- On the host side, the first answer of the restricted options is the restricted first answer. -/
theorem select_restrict_host (q : V → Bool) (v : V) : ∀ os : List (Codec V M),
    select (os.map (·.restrict q)) (·.f Orient.host) v =
      if q v then select os (·.f Orient.host) v else none
  | [] => by cases q v <;> rfl
  | c :: os => by
      rw [List.map_cons, select_cons, select_cons, select_restrict_host q v os, restrict_host]
      cases q v <;> simp

/-- On the dual side, the first answer of the restricted options is the restricted first answer,
    where every two options that answer give one value. -/
theorem select_restrict_dual (q : V → Bool) (a : V) : ∀ os : List (Codec V M),
    (∀ c ∈ os, ∀ d ∈ os, ∀ t w, c.f Orient.dual a = some t → d.f Orient.dual a = some w → t = w) →
    select (os.map (·.restrict q)) (·.f Orient.dual) a =
      (select os (·.f Orient.dual) a).bind fun y => if q y then some y else none
  | [], _ => rfl
  | c :: os, hR => by
      have hR' : ∀ c ∈ os, ∀ d ∈ os, ∀ t w, c.f Orient.dual a = some t →
          d.f Orient.dual a = some w → t = w :=
        fun c hc d hd => hR c (List.mem_cons_of_mem _ hc) d (List.mem_cons_of_mem _ hd)
      rw [List.map_cons, select_cons, select_cons, restrict_dual]
      cases hc : c.f Orient.dual a with
      | none => simpa using select_restrict_dual q a os hR'
      | some t =>
        cases hq : q t
        · have hn : select (os.map (·.restrict q)) (·.f Orient.dual) a = none := by
            refine (select_eq_none _ a _).mpr fun d hd => ?_
            obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hd
            show (d'.restrict q).f Orient.dual a = none
            rw [restrict_dual]
            cases hw : d'.f Orient.dual a with
            | none => rfl
            | some w =>
              have := hR c List.mem_cons_self d' (List.mem_cons_of_mem _ hd') t w hc hw
              subst this
              simp [hq]
          simp [hq, hn]
        · simp [hq]

/-- **The restriction distributes over the join**: over pairwise compatible options, a restriction
    of the join is the join of the restrictions. No lawfulness. -/
theorem join_restrict (q : V → Bool) (μ : Option M) {os : List (Codec V M)}
    (hC : ∀ c ∈ os, ∀ d ∈ os, Compat c d) :
    (altCodec os μ).restrict q = altCodec (os.map (·.restrict q)) μ := by
  refine Codec.ext ?_ rfl ?_ ?_
  · funext v
    apply propext
    simp only [Codec.restrict, refine2, altCodec, List.mem_map]
    constructor
    · rintro ⟨⟨c, hc, hT⟩, hq⟩
      exact ⟨_, ⟨c, hc, rfl⟩, hT, hq⟩
    · rintro ⟨_, ⟨c, hc, rfl⟩, hT, hq⟩
      exact ⟨⟨c, hc, hT⟩, hq⟩
  · funext v
    show (altCodec os μ |>.restrict q).f Orient.host v = select _ _ v
    rw [restrict_host, select_restrict_host]
    rfl
  · funext a
    show (altCodec os μ |>.restrict q).f Orient.dual a = select _ _ a
    rw [restrict_dual, select_restrict_dual q a os
      (fun c hc d hd t w ht hw => ((hC c hc d hd).p_agree ht hw).symm)]
    rfl

/-- An option that reads `0` to `1`, and `1` to `0`. With `idc`, two options read `0` to two values. -/
def swap01 : Codec Nat Unit :=
  Codec.ofEP (fun _ => True) none (fun v => some (if v = 0 then 1 else if v = 1 then 0 else v))
    (fun a => some (if a = 0 then 1 else if a = 1 then 0 else a))

/-- **The distribution needs `Compat`**: over `idc` and `swap01`, the restriction to `1` of the
    join differs from the join of the restrictions. -/
theorem restrict_join_needs_compat :
    ((altCodec [idc, swap01] none).restrict (· == 1)).f Orient.dual 0 ≠
      (altCodec ([idc, swap01].map (·.restrict (· == 1))) none).f Orient.dual 0 := by
  decide

end Join

/-! ## The ε-elimination and the graph guard -/

section Graph

/-- `all` over `List.finRange k` holds exactly where the predicate holds at every position. -/
theorem all_finRange {k : Nat} {f : Fin k → Bool} :
    (List.finRange k).all f = true ↔ ∀ p, f p = true := by
  simp [List.all_eq_true, List.mem_finRange]

/-- `any` over `List.finRange k` holds exactly where the predicate holds at one position. -/
theorem any_finRange {k : Nat} {f : Fin k → Bool} :
    (List.finRange k).any f = true ↔ ∃ p, f p = true := by
  simp [List.any_eq_true, List.mem_finRange]

/-- `all` over the positions of an operation holds exactly where the predicate holds at each. -/
theorem all_pos {o : S.Op} {f : S.Pos o → Bool} : (S.pos o).all f = true ↔ ∀ p, f p = true := by
  simp only [List.all_eq_true]; exact ⟨fun h p => h p (S.pos_complete o p), fun h p _ => h p⟩

/-- `any` over the positions of an operation holds exactly where the predicate holds at one. -/
theorem any_pos {o : S.Op} {f : S.Pos o → Bool} : (S.pos o).any f = true ↔ ∃ p, f p = true := by
  simp only [List.any_eq_true]
  exact ⟨fun ⟨p, _, h⟩ => ⟨p, h⟩, fun ⟨p, h⟩ => ⟨p, S.pos_complete o p, h⟩⟩

/-- Substitution of a term for each leaf. -/
def Flat.bind {Op : Type} {ar : Op → Type} {n m : Nat} (σ : Fin n → Flat Op ar m) :
    Flat Op ar n → Flat Op ar m
  | .leaf i => σ i
  | .node o args => .node o fun p => Flat.bind σ (args p)

/-- **The substitution lemma.** -/
theorem Flat.interp_bind {m : Nat} (e : Fin m → Codec V M) (σ : Fin n → Flat S.Op S.Pos m) :
    ∀ t : Flat S.Op S.Pos n, (t.bind σ).interp R e = t.interp R fun j => (σ j).interp R e
  | .leaf _ => rfl
  | .node o args => by
      simp only [Flat.bind, Flat.interp]
      exact congrArg (R.run o) (funext fun p => Flat.interp_bind e σ (args p))

/-- No leaf, as a decision. -/
def Flat.closedB (S : Container) : Flat S.Op S.Pos n → Bool
  | .leaf _ => false
  | .node o args => (S.pos o).all fun p => Flat.closedB S (args p)

/-- No leaf under a `wall`, as a decision. -/
def Flat.okB (S : Container) : Flat S.Op S.Pos n → Bool
  | .leaf _ => true
  | .node o args => match S.kind o with
    | .wall => (S.pos o).all fun p => Flat.closedB S (args p)
    | _ => (S.pos o).all fun p => Flat.okB S (args p)

/-- The leaf `j` sits at an unguarded position: below `keep` nodes only. -/
def Flat.ulv (S : Container) (j : Fin n) : Flat S.Op S.Pos n → Bool
  | .leaf i => decide (i = j)
  | .node o args => match S.kind o with
    | .keep => (S.pos o).any fun p => Flat.ulv S j (args p)
    | _ => false

/-- The decision of no leaf is sound. -/
theorem Flat.closed_of_closedB : ∀ t : Flat S.Op S.Pos n, t.closedB S = true → t.Closed S
  | .leaf _, h => by simp [Flat.closedB] at h
  | .node o args, h => by
      simp only [Flat.closedB] at h
      exact fun p => Flat.closed_of_closedB (args p) (all_pos.mp h p)

/-- The decision of no leaf under a wall is sound. -/
theorem Flat.ok_of_okB : ∀ t : Flat S.Op S.Pos n, t.okB S = true → t.Ok S
  | .leaf _, _ => trivial
  | .node o args, h => by
      simp only [Flat.okB] at h
      simp only [Flat.Ok]
      generalize hk : S.kind o = k at h ⊢
      cases k with
      | wall => exact fun p => Flat.closed_of_closedB _ (all_pos.mp h p)
      | keep => exact fun p => Flat.ok_of_okB _ (all_pos.mp h p)
      | down => exact fun p => Flat.ok_of_okB _ (all_pos.mp h p)

/-- No leaf under a wall and no unguarded leaf give the guard `Flat.Guarded`. -/
theorem Flat.guarded_of : ∀ t : Flat S.Op S.Pos n,
    t.okB S = true → (∀ j, t.ulv S j = false) → t.Guarded S
  | .leaf i, _, hu => by have := hu i; simp [Flat.ulv] at this
  | .node o args, h, hu => by
      simp only [Flat.okB] at h
      simp only [Flat.Guarded]
      generalize hk : S.kind o = k at h ⊢
      cases k with
      | keep =>
        refine fun p => Flat.guarded_of _ (all_pos.mp h p) fun j => ?_
        have hj := hu j
        simp only [Flat.ulv, hk] at hj
        cases hp : (args p).ulv S j
        · rfl
        · have := (any_pos (f := fun p => (args p).ulv S j)).mpr ⟨p, hp⟩
          rw [hj] at this
          exact nomatch this
      | down => exact fun p => Flat.ok_of_okB _ (all_pos.mp h p)
      | wall => exact fun p => Flat.closed_of_closedB _ (all_pos.mp h p)

/-- An unguarded leaf of a substitution is an unguarded leaf of a substituted term, at an unguarded
    leaf of the outer term. -/
theorem Flat.ulv_bind {σ : Fin n → Flat S.Op S.Pos n} {j : Fin n} :
    ∀ t : Flat S.Op S.Pos n, (t.bind σ).ulv S j = true →
      ∃ m, t.ulv S m = true ∧ (σ m).ulv S j = true
  | .leaf i, h => ⟨i, by simp [Flat.ulv], h⟩
  | .node o args, h => by
      simp only [Flat.bind, Flat.ulv] at h
      generalize hk : S.kind o = k at h
      cases k with
      | keep =>
        obtain ⟨p, hp⟩ := any_pos.mp h
        obtain ⟨m, hm, hσ⟩ := Flat.ulv_bind (args p) hp
        refine ⟨m, ?_, hσ⟩
        simp only [Flat.ulv, hk]
        exact any_pos.mpr ⟨p, hm⟩
      | down => simp at h
      | wall => simp at h

/-- A substitution keeps a term with no leaf. -/
theorem Flat.closedB_bind {σ : Fin n → Flat S.Op S.Pos n} :
    ∀ t : Flat S.Op S.Pos n, t.closedB S = true → (t.bind σ).closedB S = true
  | .leaf _, h => by simp [Flat.closedB] at h
  | .node o args, h => by
      simp only [Flat.closedB] at h
      simp only [Flat.bind, Flat.closedB]
      exact all_pos.mpr fun p => Flat.closedB_bind (args p) (all_pos.mp h p)

/-- A substitution of terms with no leaf under a wall keeps a term with no leaf under a wall. -/
theorem Flat.okB_bind {σ : Fin n → Flat S.Op S.Pos n} (hσ : ∀ m, (σ m).okB S = true) :
    ∀ t : Flat S.Op S.Pos n, t.okB S = true → (t.bind σ).okB S = true
  | .leaf i, _ => hσ i
  | .node o args, h => by
      simp only [Flat.okB] at h
      simp only [Flat.bind, Flat.okB]
      generalize hk : S.kind o = k at h ⊢
      cases k with
      | wall =>
        exact all_pos.mpr fun p => Flat.closedB_bind (args p) (all_pos.mp h p)
      | keep =>
        exact all_pos.mpr fun p => Flat.okB_bind hσ (args p) (all_pos.mp h p)
      | down =>
        exact all_pos.mpr fun p => Flat.okB_bind hσ (args p) (all_pos.mp h p)

/-- A term with no leaf under a wall reads its environment through the maps only. -/
theorem Flat.interp_f_congr (hS : R.Lawful depth) {e₁ e₂ : Fin n → Codec V M}
    (he : ∀ j, (e₁ j).f = (e₂ j).f) (t : Flat S.Op S.Pos n) (ht : t.Ok S) :
    (t.interp R e₁).f = (t.interp R e₂).f :=
  AgreeLe.eq_of_forall fun _ => Flat.ok_agree hS (fun j => AgreeLe.of_eq (he j)) t ht

/-- The body of a system: entry `i` interprets the term `sys i`. -/
def sysB (R : Step S V M) (sys : Fin n → Flat S.Op S.Pos n) (e : Fin n → Codec V M) :
    Fin n → Codec V M :=
  fun i => (sys i).interp R e

/-- **ε-elimination**, `k` rounds: substitute the system into the leaves of its own terms. Round
    `k` is the body `B^(k+1)`. Structural recursion on `k`. -/
def elim (S : Container) (sys : Fin n → Flat S.Op S.Pos n) : Nat → Fin n → Flat S.Op S.Pos n
  | 0 => sys
  | k + 1 => fun i => (sys i).bind (elim S sys k)

/-- A fixed point at the maps. -/
def IsFix (B : (Fin n → Codec V M) → Fin n → Codec V M) (e : Fin n → Codec V M) : Prop :=
  ∀ i, (e i).f = (B e i).f

/-- Round `k + 1` of the ε-elimination is the system at round `k`. -/
theorem sysB_elim_succ (sys : Fin n → Flat S.Op S.Pos n) (k : Nat) (e : Fin n → Codec V M) :
    sysB R (elim S sys (k + 1)) e = sysB R sys (sysB R (elim S sys k) e) :=
  funext fun i => Flat.interp_bind e (elim S sys k) (sys i)

/-- Each round of the ε-elimination commutes with the system. -/
theorem sysB_elim_comm (sys : Fin n → Flat S.Op S.Pos n) : ∀ k e,
    sysB R (elim S sys k) (sysB R sys e) = sysB R sys (sysB R (elim S sys k) e)
  | 0, _ => rfl
  | k + 1, e => by rw [sysB_elim_succ, sysB_elim_comm sys k e, sysB_elim_succ]

/-- Each round of the ε-elimination keeps no leaf under a wall. -/
theorem okB_elim (sys : Fin n → Flat S.Op S.Pos n) (hok : ∀ i, (sys i).okB S = true) :
    ∀ k i, (elim S sys k i).okB S = true
  | 0 => hok
  | k + 1 => fun i => Flat.okB_bind (okB_elim sys hok k) (sys i) (hok i)

/-! ### The graph of unguarded edges -/

/-- An unguarded edge: the leaf `j` sits at an unguarded position of `sys i`. -/
def UEdge (S : Container) (sys : Fin n → Flat S.Op S.Pos n) (i j : Fin n) : Prop :=
  (sys i).ulv S j = true

/-- A walk of `k` unguarded edges from `i`. -/
def WalkFrom (S : Container) (sys : Fin n → Flat S.Op S.Pos n) (k : Nat) (i : Fin n) : Prop :=
  ∃ w : Nat → Fin n, w 0 = i ∧ ∀ t < k, UEdge S sys (w t) (w (t + 1))

/-- A cycle of unguarded edges. -/
def Cycle (S : Container) (sys : Fin n → Flat S.Op S.Pos n) : Prop :=
  ∃ (w : Nat → Fin n) (m : Nat), 0 < m ∧ w m = w 0 ∧ ∀ t < m, UEdge S sys (w t) (w (t + 1))

variable {sys : Fin n → Flat S.Op S.Pos n}

/-- An unguarded edge before a walk of `k` edges is a walk of `k + 1` edges. -/
theorem walk_cons {i j : Fin n} {k : Nat} (h : UEdge S sys i j) :
    WalkFrom S sys k j → WalkFrom S sys (k + 1) i
  | ⟨w, h0, hw⟩ => ⟨fun t => match t with | 0 => i | t + 1 => w t, rfl, fun t ht => match t with
      | 0 => by show UEdge S sys i (w 0); rw [h0]; exact h
      | t + 1 => hw t (by omega)⟩

/-- A walk of `k + 1` edges is an unguarded edge before a walk of `k` edges. -/
theorem walk_tail {i : Fin n} {k : Nat} :
    WalkFrom S sys (k + 1) i → ∃ j, UEdge S sys i j ∧ WalkFrom S sys k j
  | ⟨w, h0, hw⟩ => ⟨w 1, by rw [← h0]; exact hw 0 (by omega), fun t => w (t + 1), rfl,
      fun t ht => hw (t + 1) (by omega)⟩

/-- A walk of `k + 1` edges contains a walk of `k` edges. -/
theorem walk_mono {i : Fin n} {k : Nat} : WalkFrom S sys (k + 1) i → WalkFrom S sys k i
  | ⟨w, h0, hw⟩ => ⟨w, h0, fun t ht => hw t (by omega)⟩

/-- An unguarded leaf after `k` rounds is the end of a walk of `k + 1` unguarded edges. -/
theorem ulv_elim_walk (sys : Fin n → Flat S.Op S.Pos n) :
    ∀ k i j, (elim S sys k i).ulv S j = true → WalkFrom S sys (k + 1) i
  | 0, _, j, h => walk_cons h ⟨fun _ => j, rfl, fun _ ht => absurd ht (Nat.not_lt_zero _)⟩
  | k + 1, i, j, h => by
      obtain ⟨m, hm, hσ⟩ := Flat.ulv_bind (sys i) h
      exact walk_cons hm (ulv_elim_walk sys k m j hσ)

/-- **The pigeonhole**: `n + 1` values in `Fin n` repeat. -/
theorem pigeon : ∀ (n : Nat) (w : Nat → Fin n), ∃ a b, a < b ∧ b ≤ n ∧ w a = w b
  | 0, w => (w 0).elim0
  | n + 1, w => by
      cases hdec : decide (∃ b, b < n + 1 ∧ w (b + 1) = w 0) with
      | true =>
        obtain ⟨b, hb, he⟩ := of_decide_eq_true hdec
        exact ⟨0, b + 1, by omega, by omega, he.symm⟩
      | false =>
        have hne : ∀ b, b < n + 1 → (w (b + 1)).val ≠ (w 0).val := fun b hb he =>
          absurd ⟨b, hb, Fin.ext he⟩ (of_decide_eq_false hdec)
        cases n with
        | zero =>
          exact absurd (by have := (w 1).isLt; have := (w 0).isLt; omega) (hne 0 (by omega))
        | succ n =>
          have hv := (w 0).isLt
          let sq : Nat → Fin (n + 1) := fun t =>
            if h : (w (t + 1)).val < (w 0).val then ⟨(w (t + 1)).val, by omega⟩
            else ⟨(w (t + 1)).val - 1, by have := (w (t + 1)).isLt; omega⟩
          obtain ⟨a, b, hab, hb, he⟩ := pigeon (n + 1) sq
          refine ⟨a + 1, b + 1, by omega, by omega, Fin.ext ?_⟩
          have ha' := hne a (by omega)
          have hb' := hne b (by omega)
          simp only [sq] at he
          split at he <;> split at he <;> simp only [Fin.mk.injEq] at he <;> omega

/-- A walk of `n` unguarded edges over `n` entries contains a cycle. -/
theorem cycle_of_walk {i : Fin n} (h : WalkFrom S sys n i) : Cycle S sys := by
  obtain ⟨w, -, hw⟩ := h
  obtain ⟨a, b, hab, hb, he⟩ := pigeon n w
  refine ⟨fun t => w (a + t), b - a, by omega, ?_, fun t ht => ?_⟩
  · show w (a + (b - a)) = w (a + 0)
    rw [show a + (b - a) = b by omega, Nat.add_zero]
    exact he.symm
  · show UEdge S sys (w (a + t)) (w (a + (t + 1)))
    rw [show a + (t + 1) = a + t + 1 by omega]
    exact hw _ (by omega)

/-- A cycle gives an entry with a walk of every length. -/
theorem walks_of_cycle : Cycle S sys → ∃ i, ∀ k, WalkFrom S sys k i := by
  rintro ⟨w, m, hm, hwm, hw⟩
  have key : ∀ k s, s < m → WalkFrom S sys k (w s) := by
    intro k
    induction k with
    | zero => intro s _; exact ⟨fun _ => w s, rfl, fun _ ht => absurd ht (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro s hs
      rcases Nat.lt_or_ge (s + 1) m with h | h
      · exact walk_cons (hw s hs) (ih (s + 1) h)
      · have hsm : s + 1 = m := by omega
        have he : UEdge S sys (w s) (w 0) := by rw [← hwm, ← hsm]; exact hw s hs
        exact walk_cons he (ih 0 hm)
  exact ⟨w 0, fun k => key k 0 hm⟩

/-! ### The graph guard -/

/-- A walk of `k` unguarded edges from `i`, as a decision. Structural recursion on `k`. -/
def walkB (S : Container) (sys : Fin n → Flat S.Op S.Pos n) : Nat → Fin n → Bool
  | 0 => fun _ => true
  | k + 1 => fun i => (List.finRange n).any fun j => (sys i).ulv S j && walkB S sys k j

/-- The decision of a walk is sound and complete. -/
theorem walkB_iff (sys : Fin n → Flat S.Op S.Pos n) :
    ∀ k i, walkB S sys k i = true ↔ WalkFrom S sys k i
  | 0, i => ⟨fun _ => ⟨fun _ => i, rfl, fun _ ht => absurd ht (Nat.not_lt_zero _)⟩, fun _ => rfl⟩
  | k + 1, i => by
      simp only [walkB, any_finRange, Bool.and_eq_true]
      constructor
      · rintro ⟨j, hj, hw⟩; exact walk_cons hj ((walkB_iff sys k j).mp hw)
      · intro h
        obtain ⟨j, hj, hw⟩ := walk_tail h
        exact ⟨j, hj, (walkB_iff sys k j).mpr hw⟩

/-- **The graph guard**: no leaf under a wall, and no walk of `n` unguarded edges. -/
def graphGuard (S : Container) (sys : Fin n → Flat S.Op S.Pos n) : Bool :=
  (List.finRange n).all (fun i => (sys i).okB S) && (List.finRange n).all (fun i => !walkB S sys n i)

/-- **The law of the graph guard**: the guard holds exactly where no leaf sits under a wall and no
    cycle of unguarded edges exists. -/
theorem graphGuard_iff (sys : Fin n → Flat S.Op S.Pos n) :
    graphGuard S sys = true ↔ (∀ i, (sys i).okB S = true) ∧ ¬ Cycle S sys := by
  simp only [graphGuard, Bool.and_eq_true, all_finRange]
  refine and_congr Iff.rfl ⟨fun h hc => ?_, fun h i => ?_⟩
  · obtain ⟨i, hi⟩ := walks_of_cycle hc
    have := h i
    rw [(walkB_iff sys n i).mpr (hi n)] at this
    exact nomatch this
  · cases hw : walkB S sys n i
    · rfl
    · exact absurd (cycle_of_walk ((walkB_iff sys n i).mp hw)) h

/-! ### The ε-elimination solves the system -/

/-- With no leaf under a wall and no cycle, each entry of round `n` is guarded. -/
theorem elim_guarded (hok : ∀ i, (sys i).okB S = true) (hnc : ¬ Cycle S sys) :
    ∀ i, (elim S sys n i).Guarded S := fun i =>
  Flat.guarded_of _ (okB_elim sys hok n i) fun j => by
    cases h : (elim S sys n i).ulv S j
    · rfl
    · exact absurd (cycle_of_walk (walk_mono (ulv_elim_walk sys n i j h))) hnc

/-- After `n` rounds, the system is contractive. -/
theorem elim_contractive (hS : R.Lawful depth) (hok : ∀ i, (sys i).okB S = true)
    (hnc : ¬ Cycle S sys) : ContractiveV depth (sysB R (elim S sys n)) :=
  contractive_of_guarded hS _ (elim_guarded hok hnc)

/-- With no leaf under a wall, environments with the same maps give entries with the same maps. -/
theorem sysB_congr (hS : R.Lawful depth) (hok : ∀ i, (sys i).Ok S) {e₁ e₂ : Fin n → Codec V M}
    (he : ∀ j, (e₁ j).f = (e₂ j).f) : ∀ i, (sysB R sys e₁ i).f = (sysB R sys e₂ i).f :=
  fun i => Flat.interp_f_congr hS he (sys i) (hok i)

/-- A fixed point of the system is a fixed point of each round. -/
theorem fix_elim_of_fix (hS : R.Lawful depth) (hok : ∀ i, (sys i).Ok S) {e : Fin n → Codec V M}
    (he : IsFix (sysB R sys) e) : ∀ k, IsFix (sysB R (elim S sys k)) e
  | 0 => he
  | k + 1 => fun i => by
      rw [sysB_elim_succ]
      exact (he i).trans (sysB_congr hS hok (fun j => fix_elim_of_fix hS hok he k j) i)

/-- **The ε-elimination keeps the solution**: where round `k` is guarded, the solution of round
    `k` is a fixed point of the system, and every fixed point of the system has its maps. -/
theorem elim_solution (hd : ∀ v, 0 < depth v) (hS : R.Lawful depth) (hok : ∀ i, (sys i).Ok S)
    {k : Nat} (hg : ∀ i, (elim S sys k i).Guarded S) :
    IsFix (sysB R sys) (solve depth (sysB R (elim S sys k))) ∧
      ∀ e, IsFix (sysB R sys) e → ∀ i, (e i).f = (solve depth (sysB R (elim S sys k)) i).f := by
  have hC : ContractiveV depth (sysB R (elim S sys k)) := contractive_of_guarded hS _ hg
  have hfix : IsFix (sysB R (elim S sys k)) (solve depth (sysB R (elim S sys k))) :=
    fun i => funext fun o => funext fun x => solve_fix hd hC i o x
  have huniq : ∀ e, IsFix (sysB R (elim S sys k)) e →
      ∀ i, (e i).f = (solve depth (sysB R (elim S sys k)) i).f := fun e he i =>
    AgreeLe.eq_of_forall fun d =>
      solve_unique hd hC (fun i o x => congrFun (congrFun (he i) o) x) d i
  refine ⟨fun i => ?_, fun e he => huniq e (fix_elim_of_fix hS hok he k)⟩
  have hBs : IsFix (sysB R (elim S sys k)) (sysB R sys (solve depth (sysB R (elim S sys k)))) :=
    fun j => by
      rw [sysB_elim_comm]
      exact sysB_congr hS hok hfix j
  exact (huniq _ hBs i).symm

/-- Where round `k` is guarded, the system and its round `k` have the same fixed points. -/
theorem fix_iff_elim (hd : ∀ v, 0 < depth v) (hS : R.Lawful depth) (hok : ∀ i, (sys i).Ok S)
    {k : Nat} (hg : ∀ i, (elim S sys k i).Guarded S) (e : Fin n → Codec V M) :
    IsFix (sysB R sys) e ↔ IsFix (sysB R (elim S sys k)) e := by
  refine ⟨fun he => fix_elim_of_fix hS hok he k, fun he i => ?_⟩
  have hC : ContractiveV depth (sysB R (elim S sys k)) := contractive_of_guarded hS _ hg
  have hes : ∀ j, (e j).f = (solve depth (sysB R (elim S sys k)) j).f := fun j =>
    AgreeLe.eq_of_forall fun d =>
      solve_unique hd hC (fun i o x => congrFun (congrFun (he i) o) x) d j
  rw [hes i, (elim_solution hd hS hok hg).1 i]
  exact sysB_congr hS hok (fun j => (hes j).symm) i

/-- **The theorem**: a system with no leaf under a wall and no cycle of unguarded edges has a
    solution, and only one. -/
theorem graph_solution (hd : ∀ v, 0 < depth v) (hS : R.Lawful depth)
    (hok : ∀ i, (sys i).okB S = true) (hnc : ¬ Cycle S sys) :
    ∃ s, IsFix (sysB R sys) s ∧ ∀ e, IsFix (sysB R sys) e → ∀ i, (e i).f = (s i).f :=
  ⟨_, elim_solution hd hS (fun i => Flat.ok_of_okB _ (hok i)) (elim_guarded hok hnc)⟩

/-- A system that passes `graphGuard` has a solution, and only one, at the maps. -/
theorem graphGuard_solution (hd : ∀ v, 0 < depth v) (hS : R.Lawful depth)
    (h : graphGuard S sys = true) :
    ∃ s, IsFix (sysB R sys) s ∧ ∀ e, IsFix (sysB R sys) e → ∀ i, (e i).f = (s i).f :=
  let ⟨hok, hnc⟩ := (graphGuard_iff sys).mp h
  graph_solution hd hS hok hnc

end Graph

/-! ## The step with the join and the restriction -/

section WithJoin

/-- A relation at each element relates the two images of a list pointwise. -/
theorem forall₂_map_of {α β : Type} {R : β → β → Prop} {f g : α → β} (h : ∀ a, R (f a) (g a)) :
    ∀ l : List α, List.Forall₂ R (l.map f) (l.map g)
  | [] => .nil
  | a :: l => .cons (h a) (forall₂_map_of h l)

/-- The arity of the extended step. -/
def joinArity (S : Container) (V M : Type) : S.Op ⊕ (Nat × Option M) ⊕ (V → Bool) → Type
  | .inl o => S.Pos o
  | .inr (.inl (k, _)) => Fin k
  | .inr (.inr _) => Unit

/-- The positions of the extended step, enumerated. -/
def joinPos (S : Container) (V M : Type) : (o : S.Op ⊕ (Nat × Option M) ⊕ (V → Bool)) → List (joinArity S V M o)
  | .inl o => S.pos o
  | .inr (.inl (k, _)) => List.finRange k
  | .inr (.inr _) => [()]

/-- The enumeration of the extended step holds every position. -/
theorem joinPos_complete (S : Container) (V M : Type) : ∀ o (p : joinArity S V M o), p ∈ joinPos S V M o
  | .inl o, p => S.pos_complete o p
  | .inr (.inl (_, _)), p => List.mem_finRange p
  | .inr (.inr _), () => List.mem_singleton_self ()

/-- The step with the join (`altCodec` of `k` options, member `μ`) and the restriction
    (`Codec.restrict q`). Both are `keep`. -/
def Container.withJoin (S : Container) (V M : Type) : Container where
  A := S.Op ⊕ (Nat × Option M) ⊕ (V → Bool)
  B := joinArity S V M
  pos := joinPos S V M
  pos_complete := joinPos_complete S V M
  kind
    | .inl o => S.kind o
    | .inr _ => .keep

/-- The algebra with the join and the restriction. -/
def Step.withJoin (R : Step S V M) : Step (S.withJoin V M) V M where
  run
    | .inl o, a => R.run o a
    | .inr (.inl (k, μ)), a => altCodec ((List.finRange k).map a) μ
    | .inr (.inr _q), a => (a ()).restrict _q

/-- The extension with the join and the restriction keeps the laws of the step. -/
theorem Step.Lawful.withJoin (hS : R.Lawful depth) : (R.withJoin).Lawful depth where
  keep := by
    intro o hk d a₁ a₂ h
    cases o with
    | inl o => exact hS.keep o hk d a₁ a₂ h
    | inr o =>
      cases o with
      | inl kμ => exact agreeLe_altCodec _ _ (forall₂_map_of h _)
      | inr q => exact agreeLe_restrict (h _) q
  down := by
    intro o hk d a₁ a₂ h
    cases o with
    | inl o => exact hS.down o hk d a₁ a₂ h
    | inr o => exact nomatch hk

end WithJoin

/-! ## A guarded cycle with an unguarded edge passes, and an unguarded cycle is refused -/

section Shapes

/-- One `down` operation: `shift`. -/
abbrev triSig : Container where
  A := Unit
  B _ := Fin 1
  pos _ := List.finRange 1
  pos_complete _ := List.mem_finRange
  kind _ := .down

/-- One `down` operation: `shift`, as an algebra. -/
def triStep : Step triSig Nat Unit where
  run _ a := shift (a 0)

/-- `shift` reads its argument one layer down. -/
theorem triStep_lawful : triStep.Lawful dN where
  keep _ h := nomatch h
  down _ _ d a₁ a₂ h := ⟨fun ori x hx => match x with
    | 0 => rfl
    | x + 1 => (h ⟨0, Nat.one_pos⟩).f ori x (by show x + 1 ≤ d; simp only [dN] at hx; omega)⟩

/-- `X = shift Y`, `Y = X`: `triB` as a flat system. -/
def triSys : Fin 2 → Flat triSig.Op triSig.Pos 2 := fun i => match i with
  | ⟨0, _⟩ => .node () fun _ => .leaf 1
  | ⟨_ + 1, _⟩ => .leaf 0

/-- The interpretation of `triSys` is `triB`. -/
theorem triSys_eq : sysB triStep triSys = triB := by
  funext e i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

/-- `triSys` passes the graph guard. -/
theorem tri_guard : graphGuard triSig triSys = true := by decide

/-- **`triB` has one solution**, where `solve` of `triB` breaks the fixpoint law
    (`tri_solve_not_fix`). -/
theorem tri_solution : ∃ s, IsFix triB s ∧ ∀ e, IsFix triB e → ∀ i, (e i).f = (s i).f :=
  triSys_eq ▸ graphGuard_solution (fun v => Nat.succ_pos v) triStep_lawful tri_guard

/-- The same shape with the join: `X = shift Y`, `Y = join [X, shift Y]`. -/
def triJ : Fin 2 → Flat (triSig.withJoin Nat Unit).Op (triSig.withJoin Nat Unit).Pos 2 := fun i => match i with
  | ⟨0, _⟩ => .node (.inl ()) fun _ => .leaf 1
  | ⟨_ + 1, _⟩ => .node (.inr (.inl (2, none))) fun p => match p with
    | ⟨0, _⟩ => .leaf 0
    | ⟨_ + 1, _⟩ => .node (.inl ()) fun _ => .leaf 1

/-- `triJ` passes the graph guard. -/
theorem triJ_guard : graphGuard (triSig.withJoin Nat Unit) triJ = true := by decide

/-- `triJ` has one solution, at the maps. -/
theorem triJ_solution : ∃ s, IsFix (sysB triStep.withJoin triJ) s ∧
    ∀ e, IsFix (sysB triStep.withJoin triJ) e → ∀ i, (e i).f = (s i).f :=
  graphGuard_solution (fun v => Nat.succ_pos v) triStep_lawful.withJoin triJ_guard

/-- An unguarded cycle: `Y = join [Y, ⊥]`. -/
def ctlSys : Fin 1 → Flat (triSig.withJoin Nat Unit).Op (triSig.withJoin Nat Unit).Pos 1 := fun _ =>
  .node (.inr (.inl (2, none))) fun p => match p with
    | ⟨0, _⟩ => .leaf 0
    | ⟨_ + 1, _⟩ => .node (.inr (.inl (0, none))) Fin.elim0

/-- The graph guard refuses `ctlSys`. -/
theorem ctl_refused : graphGuard (triSig.withJoin Nat Unit) ctlSys = false := by decide

/-- `ctlSys` has a cycle of unguarded edges. -/
theorem ctl_cycle : Cycle (triSig.withJoin Nat Unit) ctlSys :=
  ⟨fun _ => 0, 1, Nat.one_pos, rfl, fun _ _ => rfl⟩

/-- `idc` is a fixed point of `ctlSys`. -/
theorem ctl_fix_id : IsFix (sysB triStep.withJoin ctlSys) (fun _ => idc) := by
  intro i; funext o x; rfl

/-- The empty codec is a fixed point of `ctlSys`. -/
theorem ctl_fix_empty : IsFix (sysB triStep.withJoin ctlSys) (fun _ => .empty) := by
  intro i; funext o x; rfl

/-- **The graph guard is necessary**: `ctlSys` has two fixed points with two maps. -/
theorem ctl_unique_fails :
    ¬ ∃ s : Fin 1 → Codec Nat Unit, ∀ e, IsFix (sysB triStep.withJoin ctlSys) e → ∀ i, (e i).f = (s i).f := by
  rintro ⟨s, hs⟩
  have h := (hs _ ctl_fix_id 0).trans (hs _ ctl_fix_empty 0).symm
  have := congrFun (congrFun h Orient.host) 0
  exact nomatch this

end Shapes

/-! ## The stratified system

`SFlat w k` is a flat term whose leaves above every guard name an entry below `k`. A `down` step
widens the nameable entries to the width `w`. A `wall` step closes both indices, so no leaf sits
below a wall, also not below a `down` under a wall. -/

section Strat

/-- The width below a node: a `wall` closes it. -/
def Kind.w : Kind → Nat → Nat
  | .wall, _ => 0
  | .keep, w => w
  | .down, w => w

/-- The nameable entries below a node: `keep` keeps them, `down` widens them to the width, and
    `wall` closes them. -/
def Kind.k : Kind → Nat → Nat → Nat
  | .keep, _, k => k
  | .down, w, _ => w
  | .wall, _, _ => 0

/-- The stratified flat term. -/
inductive SFlat (Op : Type) (ar : Op → Type) (kd : Op → Kind) : Nat → Nat → Type where
  | leaf {w k : Nat} (j : Fin k) : SFlat Op ar kd w k
  | node {w k : Nat} (o : Op)
      (args : ar o → SFlat Op ar kd ((kd o).w w) ((kd o).k w k)) : SFlat Op ar kd w k

/-- **A stratified system**: entry `i` names an entry below `i` above every guard, and any entry
    below a guard. -/
abbrev SSys (S : Container) (n : Nat) : Type := (i : Fin n) → SFlat S.Op S.Pos S.kind n i

/-- The environment of the width below a node. -/
def Kind.envW {X : Type} {w : Nat} : (κ : Kind) → (Fin w → X) → Fin (κ.w w) → X
  | .keep, ρ => ρ
  | .down, ρ => ρ
  | .wall, _ => Fin.elim0

/-- The environment of the nameable entries below a node. -/
def Kind.envK {X : Type} {w k : Nat} : (κ : Kind) → (Fin w → X) → (Fin k → X) → Fin (κ.k w k) → X
  | .keep, _, ρ => ρ
  | .down, ρ, _ => ρ
  | .wall, _, _ => Fin.elim0

/-- A map commutes with the environment of the width below a node. -/
theorem Kind.envW_comp {X Y : Type} {w : Nat} (g : X → Y) :
    ∀ (κ : Kind) (ρ : Fin w → X), (fun j => g (κ.envW ρ j)) = κ.envW (fun j => g (ρ j))
  | .keep, _ => rfl
  | .down, _ => rfl
  | .wall, _ => funext fun j => j.elim0

/-- A map commutes with the environment of the nameable entries below a node. -/
theorem Kind.envK_comp {X Y : Type} {w k : Nat} (g : X → Y) :
    ∀ (κ : Kind) (ρw : Fin w → X) (ρk : Fin k → X),
      (fun j => g (κ.envK ρw ρk j)) = κ.envK (fun j => g (ρw j)) (fun j => g (ρk j))
  | .keep, _, _ => rfl
  | .down, _, _ => rfl
  | .wall, _, _ => funext fun j => j.elim0

/-- A property of each value of an environment holds at each value of the width below a node. -/
theorem Kind.envW_all {X : Type} {w : Nat} {P : X → Prop} {ρ : Fin w → X} (h : ∀ j, P (ρ j)) :
    ∀ (κ : Kind) j, P (κ.envW ρ j)
  | .keep, j => h j
  | .down, j => h j
  | .wall, j => j.elim0

/-- A property of each value of both environments holds at each nameable entry below a node. -/
theorem Kind.envK_all {X : Type} {w k : Nat} {P : X → Prop} {ρw : Fin w → X} {ρk : Fin k → X}
    (hw : ∀ j, P (ρw j)) (hk : ∀ j, P (ρk j)) : ∀ (κ : Kind) j, P (κ.envK ρw ρk j)
  | .keep, j => hk j
  | .down, j => hw j
  | .wall, j => j.elim0

/-- Below a `down`, the nameable entries are the width. -/
theorem Kind.envK_down {X : Type} {w k : Nat} {P : X → Prop} {ρw : Fin w → X} {ρk : Fin k → X}
    (hw : ∀ j, P (ρw j)) : ∀ (κ : Kind), κ = .down → ∀ j, P (κ.envK ρw ρk j)
  | .down, _, j => hw j

/-- A wall closes the width. -/
theorem Kind.w_wall {w : Nat} : ∀ κ : Kind, κ = .wall → κ.w w = 0
  | .wall, _ => rfl

/-- A wall closes the nameable entries. -/
theorem Kind.k_wall {w k : Nat} : ∀ κ : Kind, κ = .wall → κ.k w k = 0
  | .wall, _ => rfl

/-- Below a wall, the environment of the width is empty. -/
theorem Kind.envW_wall {X : Type} {w : Nat} (ρ ρ' : Fin w → X) :
    ∀ κ : Kind, κ = .wall → κ.envW ρ = κ.envW ρ'
  | .wall, _ => funext fun j => j.elim0

/-- Below a wall, the environment of the nameable entries is empty. -/
theorem Kind.envK_wall {X : Type} {w k : Nat} (ρw ρw' : Fin w → X) (ρk ρk' : Fin k → X) :
    ∀ κ : Kind, κ = .wall → κ.envK ρw ρk = κ.envK ρw' ρk'
  | .wall, _ => funext fun j => j.elim0

/-- The codec of a stratified term, over the environment of each index. -/
def SFlat.interp (R : Step S V M) : {w k : Nat} → SFlat S.Op S.Pos S.kind w k →
    (Fin w → Codec V M) → (Fin k → Codec V M) → Codec V M
  | _, _, .leaf j, _, ρk => ρk j
  | _, _, .node o args, ρw, ρk =>
      R.run o fun p => SFlat.interp R (args p) ((S.kind o).envW ρw) ((S.kind o).envK ρw ρk)

/-- Inlining: each leaf becomes a flat term. -/
def SFlat.inl {S : Container} {n : Nat} : {w k : Nat} → SFlat S.Op S.Pos S.kind w k →
    (Fin w → Flat S.Op S.Pos n) → (Fin k → Flat S.Op S.Pos n) → Flat S.Op S.Pos n
  | _, _, .leaf j, _, σk => σk j
  | _, _, .node o args, σw, σk =>
      .node o fun p => SFlat.inl (args p) ((S.kind o).envW σw) ((S.kind o).envK σw σk)

/-- **The substitution lemma** of the inlining. -/
theorem SFlat.interp_inl {n : Nat} (e : Fin n → Codec V M) : ∀ {w k : Nat}
    (t : SFlat S.Op S.Pos S.kind w k) (σw : Fin w → Flat S.Op S.Pos n)
    (σk : Fin k → Flat S.Op S.Pos n),
    (t.inl σw σk).interp R e = t.interp R (fun j => (σw j).interp R e) (fun j => (σk j).interp R e)
  | _, _, .leaf _, _, _ => rfl
  | _, _, .node o args, σw, σk => by
      simp only [SFlat.inl, SFlat.interp, Flat.interp]
      congr 1
      funext p
      rw [SFlat.interp_inl e (args p), Kind.envW_comp, Kind.envK_comp]

/-- The graph form: the stratified system as a flat system. -/
def SSys.graph (sys : SSys S n) : Fin n → Flat S.Op S.Pos n := fun i =>
  (sys i).inl Flat.leaf fun j => Flat.leaf (Fin.castLE (Nat.le_of_lt i.isLt) j)

/-! ## The normal form, one structural fold over the entries -/

/-- The table of normal forms of the entries below `m`. Entry `m` inlines, at each unguarded leaf,
    the normal form of the entry that the leaf names. Each entry is normalized once: the vector
    of step `m` is the vector of step `m - 1` with one entry pushed. -/
def nfVec (S : Container) (sys : SSys S n) : (m : Nat) → m ≤ n → Vector (Flat S.Op S.Pos n) m
  | 0, _ => #v[]
  | m + 1, h =>
      let v := nfVec S sys m (Nat.le_of_succ_le h)
      v.push ((sys ⟨m, h⟩).inl Flat.leaf fun j => v[j])

/-- The normal form of the system. -/
def nf (S : Container) (sys : SSys S n) : Fin n → Flat S.Op S.Pos n := fun i =>
  (nfVec S sys n le_rfl)[i]

/-- Entry `j` of the table at step `m` is entry `j` with the table at step `j` inlined. -/
theorem nfVec_get (sys : SSys S n) : ∀ (m : Nat) (h : m ≤ n) (j : Nat) (hj : j < m),
    (nfVec S sys m h)[j] = (sys ⟨j, by omega⟩).inl Flat.leaf fun l => (nfVec S sys j (by omega))[l]
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | m + 1, h, j, hj => by
      simp only [nfVec, Vector.getElem_push]
      rcases Decidable.em (j < m) with a | a
      · simp only [a, dite_true]
        exact nfVec_get sys m _ j a
      · have : j = m := by omega
        subst this
        simp only [a, dite_false]

/-- **The fold's law**: the normal form of entry `i` is entry `i` with the normal form of each
    entry below `i` inlined at the unguarded leaves. -/
theorem nf_eq (sys : SSys S n) (i : Fin n) :
    nf S sys i = (sys i).inl Flat.leaf fun j => nf S sys (Fin.castLE (Nat.le_of_lt i.isLt) j) := by
  obtain ⟨i, hi⟩ := i
  show (nfVec S sys n le_rfl)[i] = _
  rw [nfVec_get sys n le_rfl i hi]
  congr 1
  funext l
  show (nfVec S sys i (by omega))[l.val] = (nfVec S sys n le_rfl)[l.val]
  rw [nfVec_get sys i _ l l.isLt, nfVec_get sys n le_rfl l (by have := l.isLt; omega)]

/-- A stratified term with both indices zero has no leaf. -/
theorem SFlat.inl_closed {n : Nat} : ∀ {w k : Nat} (t : SFlat S.Op S.Pos S.kind w k),
    w = 0 → k = 0 → ∀ (σw : Fin w → Flat S.Op S.Pos n) (σk : Fin k → Flat S.Op S.Pos n),
    (t.inl σw σk).Closed S
  | _, _, .leaf j, _, hk, _, _ => by subst hk; exact j.elim0
  | _, _, .node o args, hw, hk, σw, σk => by
      simp only [SFlat.inl, Flat.Closed]
      intro p
      refine SFlat.inl_closed (args p) ?_ ?_ _ _
      · cases S.kind o <;> simp [Kind.w, hw]
      · cases S.kind o <;> simp [Kind.k, hw, hk]

/-- A node is guarded where each argument meets the guard of the kind of the node. -/
theorem Flat.guarded_node {o : S.Op} {g : S.Pos o → Flat S.Op S.Pos n}
    (hk : S.kind o = .keep → ∀ p, (g p).Guarded S) (hd : S.kind o = .down → ∀ p, (g p).Ok S)
    (hw : S.kind o = .wall → ∀ p, (g p).Closed S) : (Flat.node o g).Guarded S := by
  simp only [Flat.Guarded]
  cases h : S.kind o with
  | keep => exact hk h
  | down => exact hd h
  | wall => exact hw h

/-- A node has no leaf under a wall where each argument meets the condition of the kind. -/
theorem Flat.ok_node {o : S.Op} {g : S.Pos o → Flat S.Op S.Pos n}
    (hk : S.kind o ≠ .wall → ∀ p, (g p).Ok S)
    (hw : S.kind o = .wall → ∀ p, (g p).Closed S) : (Flat.node o g).Ok S := by
  simp only [Flat.Ok]
  cases h : S.kind o with
  | keep => exact hk (by simp [h])
  | down => exact hk (by simp [h])
  | wall => exact hw h

/-- Inlining terms with no leaf under a wall keeps no leaf under a wall. -/
theorem SFlat.inl_ok {n : Nat} : ∀ {w k : Nat} (t : SFlat S.Op S.Pos S.kind w k)
    (σw : Fin w → Flat S.Op S.Pos n) (σk : Fin k → Flat S.Op S.Pos n),
    (∀ j, (σw j).Ok S) → (∀ j, (σk j).Ok S) → (t.inl σw σk).Ok S
  | _, _, .leaf j, _, _, _, hk => hk j
  | _, _, .node o args, σw, σk, hw, hk => by
      simp only [SFlat.inl]
      refine Flat.ok_node (fun _ p => SFlat.inl_ok (args p) _ _ (Kind.envW_all hw _)
        (Kind.envK_all hw hk _)) (fun h p => SFlat.inl_closed (args p) (Kind.w_wall _ h)
        (Kind.k_wall _ h) _ _)

/-- **Inlining guarded terms at the unguarded leaves gives a guarded term.** -/
theorem SFlat.inl_guarded {n : Nat} : ∀ {w k : Nat} (t : SFlat S.Op S.Pos S.kind w k)
    (σw : Fin w → Flat S.Op S.Pos n) (σk : Fin k → Flat S.Op S.Pos n),
    (∀ j, (σw j).Ok S) → (∀ j, (σk j).Guarded S) → (t.inl σw σk).Guarded S
  | _, _, .leaf j, _, _, _, hk => hk j
  | _, _, .node o args, σw, σk, hw, hk => by
      simp only [SFlat.inl]
      refine Flat.guarded_node ?_ ?_ ?_
      · intro h p
        refine SFlat.inl_guarded (args p) _ _ (Kind.envW_all hw _) ?_
        cases hκ : S.kind o with
        | keep => exact hk
        | down => exact absurd (hκ.symm.trans h) (by simp)
        | wall => exact absurd (hκ.symm.trans h) (by simp)
      · intro h p
        exact SFlat.inl_ok (args p) _ _ (Kind.envW_all hw _) (Kind.envK_down hw _ h)
      · intro h p
        exact SFlat.inl_closed (args p) (Kind.w_wall _ h) (Kind.k_wall _ h) _ _

/-- **Each entry of the normal form is guarded.** -/
theorem nf_guarded (sys : SSys S n) : ∀ i, (nf S sys i).Guarded S := by
  intro ⟨i, hi⟩
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rw [nf_eq]
    exact SFlat.inl_guarded _ _ _ (fun _ => trivial) fun j => ih j.val j.isLt _

/-- The interpretation of the normal form is contractive, so `solve` applies. -/
theorem nf_contractive (hS : R.Lawful depth) (sys : SSys S n) :
    ContractiveV depth (sysB R (nf S sys)) :=
  contractive_of_guarded hS _ (nf_guarded sys)

end Strat


/-! ## The stratified system and its normal form have the same fixed points -/

section StratFix

/-- A kind is `keep`, `down` or `wall`. -/
theorem Kind.cases3 : ∀ κ : Kind, κ = .keep ∨ κ = .down ∨ κ = .wall
  | .keep => .inl rfl
  | .down => .inr (.inl rfl)
  | .wall => .inr (.inr rfl)

/-- A relation at each pair of values of two environments holds below a node, at the width. -/
theorem Kind.envW_all2 {X : Type} {w : Nat} {R : X → X → Prop} {ρ ρ' : Fin w → X}
    (h : ∀ j, R (ρ j) (ρ' j)) : ∀ (κ : Kind) j, R (κ.envW ρ j) (κ.envW ρ' j)
  | .keep, j => h j
  | .down, j => h j
  | .wall, j => j.elim0

/-- A relation at each pair of values of two environments holds below a node, at the nameable
    entries. -/
theorem Kind.envK_all2 {X : Type} {w k : Nat} {R : X → X → Prop} {ρw ρw' : Fin w → X}
    {ρk ρk' : Fin k → X} (hw : ∀ j, R (ρw j) (ρw' j)) (hk : ∀ j, R (ρk j) (ρk' j)) :
    ∀ (κ : Kind) j, R (κ.envK ρw ρk j) (κ.envK ρw' ρk' j)
  | .keep, j => hk j
  | .down, j => hw j
  | .wall, j => j.elim0

/-- The interpretation keeps agreement below `d`. -/
theorem SFlat.agree (hS : R.Lawful depth) {d : Nat} : ∀ {w k : Nat}
    (t : SFlat S.Op S.Pos S.kind w k) (ρw ρw' : Fin w → Codec V M) (ρk ρk' : Fin k → Codec V M),
    (∀ j, AgreeLe depth d (ρw j) (ρw' j)) → (∀ j, AgreeLe depth d (ρk j) (ρk' j)) →
    AgreeLe depth d (t.interp R ρw ρk) (t.interp R ρw' ρk')
  | _, _, .leaf j, _, _, _, _, _, hk => hk j
  | _, _, .node o args, ρw, ρw', ρk, ρk', hw, hk => by
      simp only [SFlat.interp]
      rcases Kind.cases3 (S.kind o) with hκ | hκ | hκ
      · exact hS.keep o hκ d _ _ fun p => SFlat.agree hS (args p) _ _ _ _
          (Kind.envW_all2 hw _) (Kind.envK_all2 hw hk _)
      · exact (hS.down o hκ d _ _ fun p => SFlat.agree hS (args p) _ _ _ _
          (Kind.envW_all2 hw _) (Kind.envK_all2 hw hk _)).mono (by omega)
      · rw [Kind.envW_wall ρw ρw' _ hκ, Kind.envK_wall ρw ρw' ρk ρk' _ hκ]
        exact AgreeLe.refl _ _

/-- Environments with the same maps give one map. -/
theorem SFlat.interp_f_congr (hS : R.Lawful depth) {w k : Nat}
    (t : SFlat S.Op S.Pos S.kind w k) {ρw ρw' : Fin w → Codec V M} {ρk ρk' : Fin k → Codec V M}
    (hw : ∀ j, (ρw j).f = (ρw' j).f) (hk : ∀ j, (ρk j).f = (ρk' j).f) :
    (t.interp R ρw ρk).f = (t.interp R ρw' ρk').f :=
  AgreeLe.eq_of_forall (depth := depth) fun _ =>
    SFlat.agree hS t _ _ _ _ (fun j => AgreeLe.of_eq (hw j)) (fun j => AgreeLe.of_eq (hk j))

/-- A fixed point of the stratified system, at the maps. -/
def SIsFix (R : Step S V M) (sys : SSys S n) (e : Fin n → Codec V M) : Prop :=
  ∀ i, (e i).f = ((sys i).interp R e fun j => e (Fin.castLE (Nat.le_of_lt i.isLt) j)).f

/-- The stratified system and its graph form have the same fixed points. -/
theorem sisFix_iff_graph (sys : SSys S n) (e : Fin n → Codec V M) :
    SIsFix R sys e ↔ IsFix (sysB R sys.graph) e := by
  refine forall_congr' fun i => ?_
  simp only [sysB, SSys.graph, SFlat.interp_inl, Flat.interp]

/-- The interpretation of an entry of the normal form is the entry over the earlier normal forms. -/
theorem interp_nf (sys : SSys S n) (e : Fin n → Codec V M) (i : Fin n) :
    (nf S sys i).interp R e =
      (sys i).interp R e fun j => (nf S sys (Fin.castLE (Nat.le_of_lt i.isLt) j)).interp R e := by
  rw [nf_eq, SFlat.interp_inl]
  rfl

/-- **The stratified system and its normal form have the same fixed points.** -/
theorem sisFix_iff_nf (hS : R.Lawful depth) (sys : SSys S n) (e : Fin n → Codec V M) :
    SIsFix R sys e ↔ IsFix (sysB R (nf S sys)) e := by
  constructor
  · intro he
    have key : ∀ i : Fin n, ((nf S sys i).interp R e).f = (e i).f := by
      intro ⟨i, hi⟩
      induction i using Nat.strong_induction_on with
      | _ i ih =>
        rw [interp_nf, he ⟨i, hi⟩]
        exact SFlat.interp_f_congr hS _ (fun _ => rfl) fun j => ih j.val j.isLt _
    exact fun i => (key i).symm
  · intro he i
    rw [he i]
    show ((nf S sys i).interp R e).f = _
    rw [interp_nf]
    exact SFlat.interp_f_congr hS _ (fun _ => rfl) fun j => (he _).symm

/-- **A stratified system has one solution**, at the maps. The solution is `solve` of the normal
    form. -/
theorem strat_solution (hd : ∀ v, 0 < depth v) (hS : R.Lawful depth) (sys : SSys S n) :
    SIsFix R sys (solve depth (sysB R (nf S sys))) ∧
      ∀ e, SIsFix R sys e → ∀ i, (e i).f = (solve depth (sysB R (nf S sys)) i).f := by
  have hC := nf_contractive hS sys
  refine ⟨(sisFix_iff_nf hS sys _).mpr fun i => funext fun o => funext fun x =>
    solve_fix hd hC i o x, fun e he i => ?_⟩
  have he' := (sisFix_iff_nf hS sys e).mp he
  exact AgreeLe.eq_of_forall fun d =>
    solve_unique hd hC (fun i o x => congrFun (congrFun (he' i) o) x) d i

end StratFix

/-! ## The shape of `triJ`, stratified -/

section StratShapes

/-- The shape of `triJ` as a stratified system, X before Y: `X = shift Y` names `Y` below the guard,
    and `Y = join [X, shift Y]` names `X` above it. -/
def triS : SSys (triSig.withJoin Nat Unit) 2 := fun i => match i with
  | ⟨0, _⟩ => .node (.inl ()) fun _ => .leaf (1 : Fin 2)
  | ⟨1, _⟩ => .node (.inr (.inl (2, none))) fun p => match p with
    | ⟨0, _⟩ => .leaf (0 : Fin 1)
    | ⟨_ + 1, _⟩ => .node (.inl ()) fun _ => .leaf (1 : Fin 2)

/-- `triS` has one solution, at the maps. -/
theorem triS_solution :
    SIsFix triStep.withJoin triS (solve dN (sysB triStep.withJoin (nf _ triS))) ∧
      ∀ e, SIsFix triStep.withJoin triS e →
        ∀ i, (e i).f = (solve dN (sysB triStep.withJoin (nf _ triS)) i).f :=
  strat_solution (fun v => Nat.succ_pos v) triStep_lawful.withJoin triS

/-- The graph form of `triS` is `triJ`. -/
theorem triS_graph : ∀ i, (triS.graph i).interp triStep.withJoin = (triJ i).interp triStep.withJoin := by
  intro i
  funext e
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ =>
    simp only [SSys.graph, triS, triJ, SFlat.inl, Flat.interp]
    congr 1
    funext p
    match p with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl

end StratShapes


/-! ## The stratified form and the graph guard -/

section Bridge
variable {sys : Fin n → Flat S.Op S.Pos n}

/-- A node has an unguarded leaf `j` exactly where the node is `keep` and an argument has one. -/
theorem Flat.ulv_node_iff {o : S.Op} {g : S.Pos o → Flat S.Op S.Pos n} {j : Fin n} :
    (Flat.node o g).ulv S j = true ↔ S.kind o = .keep ∧ ∃ p, (g p).ulv S j = true := by
  simp only [Flat.ulv]
  cases h : S.kind o with
  | keep => simp [S.pos_complete]
  | down => simp
  | wall => simp

/-- A node has no leaf exactly where no argument has a leaf. -/
theorem Flat.closedB_node_iff {o : S.Op} {g : S.Pos o → Flat S.Op S.Pos n} :
    (Flat.node o g).closedB S = true ↔ ∀ p, (g p).closedB S = true := by
  simp only [Flat.closedB, all_pos]

/-- The decision of no leaf under a wall, at a node. -/
theorem Flat.okB_node_iff {o : S.Op} {g : S.Pos o → Flat S.Op S.Pos n} :
    (Flat.node o g).okB S = true ↔
      (S.kind o = .wall → ∀ p, (g p).closedB S = true) ∧ (S.kind o ≠ .wall → ∀ p, (g p).okB S = true) := by
  simp only [Flat.okB]
  cases h : S.kind o with
  | keep => simp [S.pos_complete]
  | down => simp [S.pos_complete]
  | wall => simp [S.pos_complete]

/-- The decision of no leaf is complete. -/
theorem Flat.closedB_of_closed : ∀ t : Flat S.Op S.Pos n, t.Closed S → t.closedB S = true
  | .leaf _, h => h.elim
  | .node _ args, h => Flat.closedB_node_iff.mpr fun p => Flat.closedB_of_closed (args p) (h p)

/-- The decision of no leaf under a wall is complete. -/
theorem Flat.okB_of_ok : ∀ t : Flat S.Op S.Pos n, t.Ok S → t.okB S = true
  | .leaf _, _ => rfl
  | .node o args, h => by
      simp only [Flat.Ok] at h
      refine Flat.okB_node_iff.mpr ⟨fun hκ p => ?_, fun hκ p => ?_⟩
      · rw [hκ] at h; exact Flat.closedB_of_closed _ (h p)
      · cases hk : S.kind o with
        | keep => rw [hk] at h; exact Flat.okB_of_ok _ (h p)
        | down => rw [hk] at h; exact Flat.okB_of_ok _ (h p)
        | wall => exact absurd hk hκ

/-- Below a `keep`, each nameable entry is a nameable entry above the node. -/
theorem Kind.envK_keep_pt {X : Type} {w k : Nat} {ρw : Fin w → X} {ρk : Fin k → X} :
    ∀ κ : Kind, κ = .keep → ∀ l, ∃ l', κ.envK ρw ρk l = ρk l'
  | .keep, _, l => ⟨l, rfl⟩

/-- An unguarded leaf of an inlined term is an unguarded leaf of a nameable entry's term. -/
theorem SFlat.ulv_inl {n : Nat} {j : Fin n} : ∀ {w k : Nat} (t : SFlat S.Op S.Pos S.kind w k)
    (σw : Fin w → Flat S.Op S.Pos n) (σk : Fin k → Flat S.Op S.Pos n),
    (t.inl σw σk).ulv S j = true → ∃ l, (σk l).ulv S j = true
  | _, _, .leaf l, _, _, h => ⟨l, h⟩
  | _, _, .node o args, σw, σk, h => by
      obtain ⟨hκ, p, hp⟩ := Flat.ulv_node_iff.mp h
      obtain ⟨l, hl⟩ := SFlat.ulv_inl (args p) _ _ hp
      obtain ⟨l', hl'⟩ := Kind.envK_keep_pt (ρw := σw) (ρk := σk) _ hκ l
      exact ⟨l', hl' ▸ hl⟩

/-- An unguarded edge of a stratified system goes to a lower entry. -/
theorem SSys.ulv_graph (sys : SSys S n) {i j : Fin n} (h : (sys.graph i).ulv S j = true) :
    j.val < i.val := by
  obtain ⟨l, hl⟩ := SFlat.ulv_inl (sys i) _ _ h
  simp only [Flat.ulv, decide_eq_true_eq] at hl
  rw [← hl]
  exact l.isLt

/-- A stratified system has no cycle of unguarded edges. -/
theorem SSys.no_cycle (sys : SSys S n) : ¬ Cycle S sys.graph := by
  rintro ⟨w, m, hm, hwm, hw⟩
  have key : ∀ t, t ≤ m → (w t).val + t ≤ (w 0).val := by
    intro t
    induction t with
    | zero => intro _; omega
    | succ t ih =>
      intro ht
      have h1 := sys.ulv_graph (hw t (by omega))
      have h2 := ih (by omega)
      omega
  have := key m le_rfl
  rw [hwm] at this
  omega

/-- The graph form of a stratified system passes the graph guard. -/
theorem SSys.graphGuard (sys : SSys S n) : graphGuard S sys.graph = true :=
  (graphGuard_iff _).mpr ⟨fun _ => Flat.okB_of_ok _
    (SFlat.inl_ok _ _ _ (fun _ => trivial) fun _ => trivial), sys.no_cycle⟩

/-! ### No cycle gives a rank -/

/-- The greatest `k ≤ m` where `P` holds, else `0`. Structural on `m`. -/
def greatest (P : Nat → Bool) : Nat → Nat
  | 0 => 0
  | m + 1 => cond (P (m + 1)) (m + 1) (greatest P m)

/-- `greatest P m` is at most `m`. -/
theorem greatest_le (P : Nat → Bool) : ∀ m, greatest P m ≤ m
  | 0 => Nat.le_refl 0
  | m + 1 => by
      cases h : P (m + 1) with
      | true => simp only [greatest, h, cond_true]; exact Nat.le_refl _
      | false => simp only [greatest, h, cond_false]; exact Nat.le_succ_of_le (greatest_le P m)

/-- Where `P 0` holds, `P` holds at `greatest P m`. -/
theorem greatest_spec (P : Nat → Bool) (h0 : P 0 = true) : ∀ m, P (greatest P m) = true
  | 0 => h0
  | m + 1 => by
      cases h : P (m + 1) with
      | true => simp only [greatest, h, cond_true]
      | false => simp only [greatest, h, cond_false]; exact greatest_spec P h0 m

/-- Each `k ≤ m` where `P` holds is at most `greatest P m`. -/
theorem le_greatest (P : Nat → Bool) : ∀ m k, k ≤ m → P k = true → k ≤ greatest P m
  | 0, _, hk, _ => hk
  | m + 1, k, hk, hP => by
      cases h : P (m + 1) with
      | true => simp only [greatest, h, cond_true]; exact hk
      | false =>
        simp only [greatest, h, cond_false]
        rcases Nat.lt_or_ge k (m + 1) with hl | hl
        · exact le_greatest P m k (Nat.le_of_lt_succ hl) hP
        · have hkm : k = m + 1 := Nat.le_antisymm hk hl
          rw [hkm, h] at hP
          exact nomatch hP

/-- No cycle gives a rank that every unguarded edge lowers: the length of the longest walk. -/
theorem rank_of_noCycle (hnc : ¬ Cycle S sys) :
    ∃ r : Fin n → Nat, ∀ i j, UEdge S sys i j → r j < r i := by
  refine ⟨fun i => greatest (fun k => walkB S sys k i) n, fun i j hij => ?_⟩
  have hj : walkB S sys (greatest (fun k => walkB S sys k j) n) j = true :=
    greatest_spec (fun k => walkB S sys k j) rfl n
  have hwi : walkB S sys (greatest (fun k => walkB S sys k j) n + 1) i = true :=
    (walkB_iff sys _ i).mpr (walk_cons hij ((walkB_iff sys _ j).mp hj))
  have hkn : greatest (fun k => walkB S sys k j) n + 1 ≤ n := by
    rcases Nat.lt_or_ge (greatest (fun k => walkB S sys k j) n) n with h | h
    · omega
    · have he := Nat.le_antisymm (greatest_le _ n) h
      rw [he] at hj
      exact absurd (cycle_of_walk ((walkB_iff sys n j).mp hj)) hnc
  exact le_greatest _ n _ hkn hwi

end Bridge

/-! ## A DAG of scopes

A scope of `n` entries after `c` earlier entries is a stratified system over the step with one
nullary `keep` operation per earlier entry: a **constant**. A constant has no leaf, so it may sit
at any position, a wall included. A system is a sequence of scopes. -/

section Scopes

/-- The arity of the step with `c` constants: a constant takes no argument. -/
def cAr (S : Container) (c : Nat) : S.Op ⊕ Fin c → Type
  | .inl o => S.Pos o
  | .inr _ => Empty

/-- The positions of the step with `c` constants, enumerated. -/
def cPos (S : Container) (c : Nat) : (o : S.Op ⊕ Fin c) → List (cAr S c o)
  | .inl o => S.pos o
  | .inr _ => []

/-- The enumeration of the step with constants holds every position. -/
theorem cPos_complete (S : Container) (c : Nat) : ∀ o (p : cAr S c o), p ∈ cPos S c o
  | .inl o, p => S.pos_complete o p
  | .inr _, p => nomatch p

/-- The kind of the step with `c` constants: a constant is `keep`. -/
def cKd (S : Container) (c : Nat) : S.Op ⊕ Fin c → Kind
  | .inl o => S.kind o
  | .inr _ => .keep

/-- **The step with constants**: constant `j` denotes `κ j`. The syntax does not read `κ`. -/
def cSig (S : Container) (c : Nat) : Container where
  A := S.Op ⊕ Fin c
  B := cAr S c
  pos := cPos S c
  pos_complete := cPos_complete S c
  kind := cKd S c

/-- **The algebra with constants**: constant `j` denotes `κ j`. -/
def CStep (R : Step S V M) (c : Nat) (κ : Fin c → Codec V M) : Step (cSig S c) V M where
  run
    | .inl o, a => R.run o a
    | .inr j, _ => κ j

/-- **A scope**: a stratified system of `n` entries over the step with `c` constants. -/
abbrev Scope (S : Container) (c n : Nat) : Type :=
  (i : Fin n) → SFlat (S.Op ⊕ Fin c) (cAr S c) (cKd S c) n i

/-- **A DAG of scopes**: each scope reads the entries of the scopes before it as constants. -/
inductive DSys (S : Container) : Nat → Type where
  | nil : DSys S 0
  | snoc {c n : Nat} (d : DSys S c) (sc : Scope S c n) : DSys S (c + n)

/-- The step with constants keeps the laws of the step: a constant reads no argument. -/
theorem CStep.lawful (hS : R.Lawful depth) (c : Nat) (κ : Fin c → Codec V M) :
    (CStep R c κ).Lawful depth where
  keep o hk d a₁ a₂ h := by
    cases o with
    | inl o => exact hS.keep o hk d a₁ a₂ h
    | inr j => exact AgreeLe.refl _ _
  down o hk d a₁ a₂ h := by
    cases o with
    | inl o => exact hS.down o hk d a₁ a₂ h
    | inr j => exact nomatch hk

/-! ## The solution, scope by scope -/

/-- **The solution**: the solution of each scope is `solve` of its normal form, with the solution of
    the scopes before it as the constants. Structural on the sequence. -/
def DSys.sol (R : Step S V M) (depth : V → Nat) : {N : Nat} → DSys S N → Fin N → Codec V M
  | _, .nil => Fin.elim0
  | _, .snoc (c := c) d sc =>
      Fin.append (DSys.sol R depth d)
        (solve depth (sysB (CStep R c (DSys.sol R depth d)) (nf (cSig S c) sc)))

/-- Inlining a scope term: an entry leaf and a constant each become a flat term of the whole. -/
def SFlat.inlC {S : Container} {c N : Nat} : {w k : Nat} →
    SFlat (S.Op ⊕ Fin c) (cAr S c) (cKd S c) w k →
    (Fin w → Flat S.Op S.Pos N) → (Fin k → Flat S.Op S.Pos N) →
    (Fin c → Flat S.Op S.Pos N) → Flat S.Op S.Pos N
  | _, _, .leaf j, _, σk, _ => σk j
  | _, _, .node (.inl o) args, σw, σk, σc =>
      .node o fun p => SFlat.inlC (args p) ((S.kind o).envW σw) ((S.kind o).envK σw σk) σc
  | _, _, .node (.inr j) _, _, _, σc => σc j

/-- **The graph form**: the DAG of scopes as one flat system, where a constant is a leaf. -/
def DSys.graph : {N : Nat} → DSys S N → Fin N → Flat S.Op S.Pos N
  | _, .nil => Fin.elim0
  | _, .snoc (c := c) (n := n) d sc => Fin.append
      (fun m => (DSys.graph d m).bind fun j => .leaf (Fin.castAdd n j))
      (fun i => (sc i).inlC (fun j => .leaf (Fin.natAdd c j))
        (fun j => .leaf (Fin.natAdd c (Fin.castLE (Nat.le_of_lt i.isLt) j)))
        (fun j => .leaf (Fin.castAdd n j)))

/-- The substitution lemma of the inlining. -/
theorem SFlat.interp_inlC {c N : Nat} (e : Fin N → Codec V M) : ∀ {w k : Nat}
    (t : SFlat (S.Op ⊕ Fin c) (cAr S c) (cKd S c) w k) (σw : Fin w → Flat S.Op S.Pos N)
    (σk : Fin k → Flat S.Op S.Pos N) (σc : Fin c → Flat S.Op S.Pos N),
    (t.inlC σw σk σc).interp R e =
      SFlat.interp (CStep R c fun j => (σc j).interp R e) t (fun j => (σw j).interp R e)
        (fun j => (σk j).interp R e)
  | _, _, .leaf _, _, _, _ => rfl
  | _, _, .node (.inl o) args, σw, σk, σc => by
      show R.run o (fun p => ((args p).inlC _ _ σc).interp R e) = R.run o _
      congr 1
      funext p
      exact (SFlat.interp_inlC e (args p) _ _ σc).trans
        (congrArg₂ (SFlat.interp (CStep R c fun j => (σc j).interp R e) (args p))
          (Kind.envW_comp _ _ _) (Kind.envK_comp _ _ _ _))
  | _, _, .node (.inr _) _, _, _, _ => rfl

/-- **What a wall owes, at the maps**: a wall reads its arguments through their maps. The walls
    of the term layer, `held` and `legacy`, do. -/
def WallF (R : Step S V M) : Prop :=
  ∀ o, S.kind o = .wall → ∀ a₁ a₂ : S.Pos o → Codec V M,
    (∀ p, (a₁ p).f = (a₂ p).f) → (R.run o a₁).f = (R.run o a₂).f

/-- Each operation reads its arguments through their maps. -/
theorem Step.run_f (hS : R.Lawful depth) (hW : WallF R) (o : S.Op)
    {a₁ a₂ : S.Pos o → Codec V M} (h : ∀ p, (a₁ p).f = (a₂ p).f) :
    (R.run o a₁).f = (R.run o a₂).f := by
  rcases Kind.cases3 (S.kind o) with hκ | hκ | hκ
  · exact AgreeLe.eq_of_forall (depth := depth) fun d =>
      hS.keep o hκ d _ _ fun p => AgreeLe.of_eq (h p)
  · exact AgreeLe.eq_of_forall (depth := depth) fun d =>
      (hS.down o hκ d _ _ fun p => AgreeLe.of_eq (h p)).mono (by omega)
  · exact hW o hκ _ _ h

/-- A flat term, a leaf below a wall included, reads its environment through the maps. -/
theorem Flat.interp_f_congrW (hS : R.Lawful depth) (hW : WallF R) {e₁ e₂ : Fin n → Codec V M}
    (he : ∀ j, (e₁ j).f = (e₂ j).f) : ∀ t : Flat S.Op S.Pos n,
    (t.interp R e₁).f = (t.interp R e₂).f
  | .leaf j => he j
  | .node o args => Step.run_f hS hW o fun p => Flat.interp_f_congrW hS hW he (args p)

/-- An entry of an earlier scope reads the graph form of the earlier scopes. -/
theorem DSys.graph_castAdd {c n : Nat} (d : DSys S c) (sc : Scope S c n) (e : Fin (c + n) → Codec V M)
    (m : Fin c) : sysB R (DSys.snoc d sc).graph e (Fin.castAdd n m) =
      sysB R d.graph (fun j => e (Fin.castAdd n j)) m := by
  simp only [sysB, DSys.graph, Fin.append_left, Flat.interp_bind, Flat.interp]

/-- An entry of the last scope reads its scope term, with the earlier entries as constants. -/
theorem DSys.graph_natAdd {c n : Nat} (d : DSys S c) (sc : Scope S c n) (e : Fin (c + n) → Codec V M)
    (i : Fin n) (κ : Fin c → Codec V M) (hκ : ∀ j, e (Fin.castAdd n j) = κ j) :
    sysB R (DSys.snoc d sc).graph e (Fin.natAdd c i) =
      SFlat.interp (CStep R c κ) (sc i) (fun j => e (Fin.natAdd c j))
        (fun j => e (Fin.natAdd c (Fin.castLE (Nat.le_of_lt i.isLt) j))) := by
  obtain rfl : (fun j => e (Fin.castAdd n j)) = κ := funext hκ
  simp only [sysB, DSys.graph, Fin.append_right, SFlat.interp_inlC, Flat.interp]

/-- **A DAG of scopes has one solution**, at the maps. The solution is the fold of
    `strat_solution`, scope by scope. -/
theorem dsys_solution (hd : ∀ v, 0 < depth v) (hS : R.Lawful depth) (hW : WallF R) :
    ∀ {N : Nat} (d : DSys S N), IsFix (sysB R d.graph) (d.sol R depth) ∧
      ∀ e, IsFix (sysB R d.graph) e → ∀ i, (e i).f = (d.sol R depth i).f
  | _, .nil => ⟨fun i => i.elim0, fun _ _ i => i.elim0⟩
  | _, .snoc (c := c) (n := n) d sc => by
      obtain ⟨ih1, ih2⟩ := dsys_solution hd hS hW d
      have hsc := strat_solution hd (CStep.lawful hS c (d.sol R depth)) sc
      refine ⟨fun i => ?_, fun e he i => ?_⟩
      · refine Fin.addCases (fun m => ?_) (fun i => ?_) i
        · rw [DSys.graph_castAdd]
          simp only [DSys.sol, Fin.append_left]
          exact ih1 m
        · rw [DSys.graph_natAdd d sc _ i (d.sol R depth) fun j => by
            simp only [DSys.sol, Fin.append_left]]
          simp only [DSys.sol, Fin.append_right]
          exact hsc.1 i
      · have he1 : IsFix (sysB R d.graph) fun j => e (Fin.castAdd n j) := fun m => by
          rw [he (Fin.castAdd n m), DSys.graph_castAdd]
        have hl := ih2 _ he1
        let e' : Fin (c + n) → Codec V M := Fin.append (d.sol R depth) fun i => e (Fin.natAdd c i)
        have hee' : ∀ j, (e j).f = (e' j).f := fun j =>
          Fin.addCases (fun m => by simp only [e', Fin.append_left]; exact hl m)
            (fun i => by simp only [e', Fin.append_right]) j
        have hfix : SIsFix (CStep R c (d.sol R depth)) sc fun i => e (Fin.natAdd c i) := by
          intro i
          rw [he (Fin.natAdd c i)]
          refine (Flat.interp_f_congrW hS hW hee' ((DSys.snoc d sc).graph (Fin.natAdd c i))).trans ?_
          have h2 := DSys.graph_natAdd (R := R) d sc e' i (d.sol R depth) fun j => by
            simp only [e', Fin.append_left]
          simp only [sysB] at h2
          rw [h2]
          simp only [e', Fin.append_right]
        refine Fin.addCases (fun m => ?_) (fun i => ?_) i
        · simp only [DSys.sol, Fin.append_left]; exact hl m
        · simp only [DSys.sol, Fin.append_right]
          exact hsc.2 _ hfix i

/-- Every entry of the solution is a `solve` entry: its held set is its write domain, and its
    member is `⊤`. So the maps fix the codec. -/
theorem DSys.sol_eq : ∀ {N : Nat} (d : DSys S N) (i : Fin N) {c : Codec V M},
    (∀ v, c.T v = ((c.e v).isSome = true)) → c.μ = none → (d.sol R depth i).f = c.f →
    d.sol R depth i = c
  | _, .nil, i, _, _, _, _ => i.elim0
  | _, .snoc (n := n) d sc, i, c, hT, hμ, hf => by
      revert hf
      refine Fin.addCases (fun m => ?_) (fun i => ?_) i
      · simp only [DSys.sol, Fin.append_left]; exact DSys.sol_eq d m hT hμ
      · simp only [DSys.sol, Fin.append_right]; exact solve_eq hT hμ

end Scopes


/-! ## The guard of a DAG of scopes: a wall names an entry outside its own component -/

section DagBridge

/-- The leaf `j` occurs at any position. -/
def Flat.lv (S : Container) (j : Fin n) : Flat S.Op S.Pos n → Bool
  | .leaf i => decide (i = j)
  | .node o args => (S.pos o).any fun p => Flat.lv S j (args p)

/-- The leaf `j` occurs below a wall. -/
def Flat.wlv (S : Container) (j : Fin n) : Flat S.Op S.Pos n → Bool
  | .leaf _ => false
  | .node o args => match S.kind o with
    | .wall => (S.pos o).any fun p => Flat.lv S j (args p)
    | _ => (S.pos o).any fun p => Flat.wlv S j (args p)

/-- A reference edge: entry `i` names entry `j` at any position. -/
def REdge (sys : Fin n → Flat S.Op S.Pos n) (i j : Fin n) : Prop := (sys i).lv S j = true

/-- **The guard of a DAG of scopes**: no cycle of unguarded edges, and a wall names only an entry
    that does not reach back, so an entry outside the component of the wall. -/
structure DagGuard (S : Container) (sys : Fin n → Flat S.Op S.Pos n) : Prop where
  noCycle : ¬ Cycle S sys
  wall : ∀ i j, (sys i).wlv S j = true → ¬ Relation.ReflTransGen (REdge sys) j i

/-- A node has the leaf `j` exactly where an argument has the leaf `j`. -/
theorem Flat.lv_node {o : S.Op} {g : S.Pos o → Flat S.Op S.Pos n} {j : Fin n} :
    (Flat.node o g).lv S j = true ↔ ∃ p, (g p).lv S j = true := by
  simp only [Flat.lv]; exact any_pos

/-- An unguarded leaf is a leaf. -/
theorem Flat.lv_of_ulv {j : Fin n} : ∀ t : Flat S.Op S.Pos n, t.ulv S j = true → t.lv S j = true
  | .leaf _, h => by simpa [Flat.ulv, Flat.lv] using h
  | .node o args, h => by
      obtain ⟨_, p, hp⟩ := Flat.ulv_node_iff.mp h
      exact Flat.lv_node.mpr ⟨p, Flat.lv_of_ulv _ hp⟩

/-- A node has the leaf `j` below a wall exactly where the node is a wall over the leaf, or an
    argument has the leaf below a wall. -/
theorem Flat.wlv_node {o : S.Op} {g : S.Pos o → Flat S.Op S.Pos n} {j : Fin n} :
    (Flat.node o g).wlv S j = true ↔
      (S.kind o = .wall ∧ ∃ p, (g p).lv S j = true) ∨ (S.kind o ≠ .wall ∧ ∃ p, (g p).wlv S j = true) := by
  simp only [Flat.wlv]
  cases S.kind o <;> simp [S.pos_complete]

/-- A walk of `m` reference edges from `i` to `j`. -/
def RWalk (sys : Fin n → Flat S.Op S.Pos n) (m : Nat) (i j : Fin n) : Prop :=
  ∃ w : Nat → Fin n, w 0 = i ∧ w m = j ∧ ∀ t < m, REdge sys (w t) (w (t + 1))

/-- A reference edge before a walk of `m` edges is a walk of `m + 1` edges. -/
theorem rwalk_cons {sys : Fin n → Flat S.Op S.Pos n} {i l j : Fin n} {m : Nat}
    (h : REdge sys i l) : RWalk sys m l j → RWalk sys (m + 1) i j
  | ⟨w, h0, hm, hw⟩ => ⟨fun t => match t with | 0 => i | t + 1 => w t, rfl, hm, fun t ht => match t with
      | 0 => by show REdge sys i (w 0); rw [h0]; exact h
      | t + 1 => hw t (by omega)⟩

/-- A walk of reference edges is a reach. -/
theorem rtg_of_rwalk {sys : Fin n → Flat S.Op S.Pos n} {j : Fin n} : ∀ (m : Nat) (i : Fin n),
    RWalk sys m i j → Relation.ReflTransGen (REdge sys) i j
  | 0, _, ⟨w, h0, hm, _⟩ => by subst h0; subst hm; exact .refl
  | m + 1, i, ⟨w, h0, hm, hw⟩ => by
      have h1 : REdge sys i (w 1) := by rw [← h0]; exact hw 0 (Nat.succ_pos m)
      exact .head h1 (rtg_of_rwalk m (w 1) ⟨fun t => w (t + 1), rfl, hm, fun t ht => hw (t + 1) (by omega)⟩)

/-- A reach is a walk of reference edges. -/
theorem rwalk_of_rtg {sys : Fin n → Flat S.Op S.Pos n} {i j : Fin n}
    (h : Relation.ReflTransGen (REdge sys) i j) : ∃ m, RWalk sys m i j := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, fun _ => j, rfl, rfl, fun _ ht => absurd ht (Nat.not_lt_zero _)⟩
  | head hab _ ih =>
    obtain ⟨m, hw⟩ := ih
    exact ⟨m + 1, rwalk_cons hab hw⟩

/-- A walk over `n` entries has a walk of at most `n` edges between its ends: cut each repeat. -/
theorem rwalk_short {sys : Fin n → Flat S.Op S.Pos n} {i j : Fin n} :
    ∀ m, RWalk sys m i j → ∃ m', m' ≤ n ∧ RWalk sys m' i j := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro ⟨w, h0, hm, hw⟩
  rcases Nat.lt_or_ge n m with hnm | hnm
  · obtain ⟨a, b, hab, hb, he⟩ := pigeon n w
    refine ih (m - (b - a)) (by omega) ⟨fun t => if t ≤ a then w t else w (t + (b - a)), ?_, ?_, ?_⟩
    · show (if 0 ≤ a then w 0 else w (0 + (b - a))) = i
      rw [if_pos (Nat.zero_le a)]
      exact h0
    · show (if m - (b - a) ≤ a then w (m - (b - a)) else w (m - (b - a) + (b - a))) = j
      rw [if_neg (show ¬ m - (b - a) ≤ a by omega), show m - (b - a) + (b - a) = m by omega]
      exact hm
    · intro t ht
      show REdge sys (if t ≤ a then w t else w (t + (b - a)))
        (if t + 1 ≤ a then w (t + 1) else w (t + 1 + (b - a)))
      rcases Nat.lt_or_ge t a with h1 | h1
      · rw [if_pos (Nat.le_of_lt h1), if_pos (show t + 1 ≤ a from h1)]
        exact hw t (by omega)
      · rcases Nat.eq_or_lt_of_le h1 with h2 | h2
        · rw [if_pos (show t ≤ a by omega), if_neg (show ¬ t + 1 ≤ a by omega), ← h2, he,
            show a + 1 + (b - a) = b + 1 by omega]
          exact hw b (by omega)
        · rw [if_neg (show ¬ t ≤ a by omega), if_neg (show ¬ t + 1 ≤ a by omega),
            show t + 1 + (b - a) = t + (b - a) + 1 by omega]
          exact hw _ (by omega)
  · exact ⟨m, hnm, w, h0, hm, hw⟩

/-- Reach in at most `k` reference edges, as a decision. Structural on `k`. -/
def reachB (sys : Fin n → Flat S.Op S.Pos n) : Nat → Fin n → Fin n → Bool
  | 0 => fun i j => decide (i = j)
  | k + 1 => fun i j =>
      decide (i = j) || (List.finRange n).any fun l => (sys i).lv S l && reachB sys k l j

/-- The decision of reach in at most `k` edges is sound and complete. -/
theorem reachB_iff (sys : Fin n → Flat S.Op S.Pos n) : ∀ (k : Nat) (i j : Fin n),
    reachB sys k i j = true ↔ ∃ m, m ≤ k ∧ RWalk sys m i j
  | 0, i, j => by
      simp only [reachB, decide_eq_true_eq]
      constructor
      · intro h
        exact ⟨0, Nat.le_refl 0, fun _ => i, rfl, h, fun _ ht => absurd ht (Nat.not_lt_zero _)⟩
      · rintro ⟨m, hm, w, h0, hmj, _⟩
        have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
        subst hm0
        exact h0.symm.trans hmj
  | k + 1, i, j => by
      simp only [reachB, Bool.or_eq_true, decide_eq_true_eq, any_finRange, Bool.and_eq_true]
      constructor
      · rintro (h | ⟨l, hl, hr⟩)
        · exact ⟨0, Nat.zero_le _, fun _ => i, rfl, h, fun _ ht => absurd ht (Nat.not_lt_zero _)⟩
        · obtain ⟨m, hm, hw⟩ := (reachB_iff sys k l j).mp hr
          exact ⟨m + 1, Nat.succ_le_succ hm, rwalk_cons hl hw⟩
      · rintro ⟨m, hm, w, h0, hmj, hw⟩
        cases m with
        | zero => exact .inl (h0.symm.trans hmj)
        | succ m =>
          refine .inr ⟨w 1, ?_, (reachB_iff sys k (w 1) j).mpr ⟨m, Nat.le_of_succ_le_succ hm,
            fun t => w (t + 1), rfl, hmj, fun t ht => hw (t + 1) (by omega)⟩⟩
          rw [← h0]
          exact hw 0 (Nat.succ_pos m)

/-- **Reach is decided structurally**: reach equals reach in at most `n` reference edges. -/
theorem reach_iff (sys : Fin n → Flat S.Op S.Pos n) (i j : Fin n) :
    Relation.ReflTransGen (REdge sys) i j ↔ reachB sys n i j = true := by
  constructor
  · intro h
    obtain ⟨m, hw⟩ := rwalk_of_rtg h
    obtain ⟨m', hm', hw'⟩ := rwalk_short m hw
    exact (reachB_iff sys n i j).mpr ⟨m', hm', hw'⟩
  · intro h
    obtain ⟨m, _, hw⟩ := (reachB_iff sys n i j).mp h
    exact rtg_of_rwalk m i hw

end DagBridge

/-! ## A renaming and a rank -/

section Rename
variable {S : Container} {R : Step S V M}

/-- The fixed points of a renamed system are the renamed fixed points. -/
theorem isFix_rename {sys g : Fin n → Flat S.Op S.Pos n} (π : Equiv.Perm (Fin n))
    (hg : ∀ m, g m = (sys (π.symm m)).bind fun j => .leaf (π j)) (e : Fin n → Codec V M) :
    IsFix (sysB R g) e ↔ IsFix (sysB R sys) fun i => e (π i) := by
  have hi : ∀ m, (sysB R g e m) = sysB R sys (fun i => e (π i)) (π.symm m) := fun m => by
    simp only [sysB, hg, Flat.interp_bind, Flat.interp]
  constructor
  · intro h i
    have := h (π i)
    rw [hi, Equiv.symm_apply_apply] at this
    exact this
  · intro h m
    rw [hi]
    have := h (π.symm m)
    simp only [Equiv.apply_symm_apply] at this
    exact this

/-- A rank that every unguarded edge lowers rules out a cycle. -/
theorem noCycle_of_rank {n : Nat} {S : Container} {sys : Fin n → Flat S.Op S.Pos n}
    (r : Fin n → Nat) (hr : ∀ i j, UEdge S sys i j → r j < r i) : ¬ Cycle S sys := by
  rintro ⟨w, m, hm, hwm, hw⟩
  have key : ∀ t, t ≤ m → r (w t) + t ≤ r (w 0) := by
    intro t
    induction t with
    | zero => intro _; omega
    | succ t ih =>
      intro ht
      have h1 := hr _ _ (hw t (by omega))
      have h2 := ih (by omega)
      omega
  have := key m le_rfl
  rw [hwm] at this
  omega


/-! ## The guard of a DAG of scopes, as a decision, and its converse -/

/-- **The guard of a DAG of scopes, as a decision**: no walk of `n` unguarded edges, and no wall
    names an entry that reaches back. Structural. -/
def dagGuardB (S : Container) (sys : Fin n → Flat S.Op S.Pos n) : Bool :=
  (List.finRange n).all (fun i => !walkB S sys n i) &&
    (List.finRange n).all fun i => (List.finRange n).all fun j =>
      !((sys i).wlv S j && reachB sys n j i)

/-- **The decision states the guard of a DAG of scopes.** -/
theorem dagGuardB_iff {sys : Fin n → Flat S.Op S.Pos n} : dagGuardB S sys = true ↔ DagGuard S sys := by
  simp only [dagGuardB, Bool.and_eq_true, all_finRange, Bool.not_eq_true']
  constructor
  · intro h
    refine ⟨fun hc => ?_, fun i j hw hr => ?_⟩
    · obtain ⟨i, hi⟩ := walks_of_cycle hc
      have := h.1 i
      rw [(walkB_iff sys n i).mpr (hi n)] at this
      exact nomatch this
    · have := h.2 i j
      rw [hw, (reach_iff sys j i).mp hr] at this
      exact nomatch this
  · intro hG
    refine ⟨fun i => ?_, fun i j => ?_⟩
    · cases hw : walkB S sys n i
      · rfl
      · exact absurd (cycle_of_walk ((walkB_iff sys n i).mp hw)) hG.noCycle
    · cases hw : (sys i).wlv S j
      · rfl
      · cases hr : reachB sys n j i
        · rfl
        · exact absurd ((reach_iff sys j i).mpr hr) (hG.wall i j hw)

/-- A wall closes the width: below a wall, no entry of the width remains. -/
theorem Kind.w_empty {w : Nat} : ∀ κ : Kind, κ = .wall → Fin (κ.w w) → False
  | .wall, _, l => l.elim0

/-- A wall closes the nameable entries. -/
theorem Kind.k_empty {w k : Nat} : ∀ κ : Kind, κ = .wall → Fin (κ.k w k) → False
  | .wall, _, l => l.elim0

/-- Each entry of the width below a node is an entry of the width above it. -/
theorem Kind.envW_some {X : Type} {w : Nat} (ρ : Fin w → X) :
    ∀ (κ : Kind) (l : Fin (κ.w w)), ∃ l', κ.envW ρ l = ρ l'
  | .keep, l => ⟨l, rfl⟩
  | .down, l => ⟨l, rfl⟩
  | .wall, l => l.elim0

/-- Each nameable entry below a node is an entry of the width or a nameable entry above it. -/
theorem Kind.envK_some {X : Type} {w k : Nat} (ρw : Fin w → X) (ρk : Fin k → X) :
    ∀ (κ : Kind) (l : Fin (κ.k w k)), (∃ l', κ.envK ρw ρk l = ρw l') ∨ ∃ l', κ.envK ρw ρk l = ρk l'
  | .keep, l => .inr ⟨l, rfl⟩
  | .down, l => .inl ⟨l, rfl⟩
  | .wall, l => l.elim0

section Leaves
variable {c N : Nat}

/-- A leaf of an inlined scope term is an entry of the width, a nameable entry, or a constant. -/
theorem SFlat.lv_inlC {j : Fin N} : ∀ {w k : Nat}
    (t : SFlat (S.Op ⊕ Fin c) (cAr S c) (cKd S c) w k) (ρw : Fin w → Fin N) (ρk : Fin k → Fin N)
    (ρc : Fin c → Fin N),
    (t.inlC (fun l => .leaf (ρw l)) (fun l => .leaf (ρk l)) (fun l => .leaf (ρc l))).lv S j = true →
      (∃ l, ρw l = j) ∨ (∃ l, ρk l = j) ∨ ∃ l, ρc l = j
  | _, _, .leaf l, _, _, _, h => .inr (.inl ⟨l, by simpa [SFlat.inlC, Flat.lv] using h⟩)
  | _, _, .node (.inr l) _, _, _, _, h => .inr (.inr ⟨l, by simpa [SFlat.inlC, Flat.lv] using h⟩)
  | _, _, .node (.inl o) args, ρw, ρk, ρc, h => by
      obtain ⟨p, hp⟩ := Flat.lv_node.mp h
      rw [← Kind.envW_comp, ← Kind.envK_comp] at hp
      rcases SFlat.lv_inlC (args p) _ _ ρc hp with ⟨l, hl⟩ | ⟨l, hl⟩ | hc
      · obtain ⟨l', hl'⟩ := Kind.envW_some ρw (S.kind o) l
        exact .inl ⟨l', hl' ▸ hl⟩
      · rcases Kind.envK_some ρw ρk (S.kind o) l with ⟨l', hl'⟩ | ⟨l', hl'⟩
        · exact .inl ⟨l', hl' ▸ hl⟩
        · exact .inr (.inl ⟨l', hl' ▸ hl⟩)
      · exact .inr (.inr hc)

/-- An unguarded leaf of an inlined scope term is a nameable entry or a constant. -/
theorem SFlat.ulv_inlC {j : Fin N} : ∀ {w k : Nat}
    (t : SFlat (S.Op ⊕ Fin c) (cAr S c) (cKd S c) w k) (ρw : Fin w → Fin N) (ρk : Fin k → Fin N)
    (ρc : Fin c → Fin N),
    (t.inlC (fun l => .leaf (ρw l)) (fun l => .leaf (ρk l)) (fun l => .leaf (ρc l))).ulv S j = true →
      (∃ l, ρk l = j) ∨ ∃ l, ρc l = j
  | _, _, .leaf l, _, _, _, h => .inl ⟨l, by simpa [SFlat.inlC, Flat.ulv] using h⟩
  | _, _, .node (.inr l) _, _, _, _, h => .inr ⟨l, by simpa [SFlat.inlC, Flat.ulv] using h⟩
  | _, _, .node (.inl o) args, ρw, ρk, ρc, h => by
      obtain ⟨hκ, p, hp⟩ := Flat.ulv_node_iff.mp h
      rw [← Kind.envW_comp, ← Kind.envK_comp] at hp
      rcases SFlat.ulv_inlC (args p) _ _ ρc hp with ⟨l, hl⟩ | hc
      · obtain ⟨l', hl'⟩ := Kind.envK_keep_pt (ρw := ρw) (ρk := ρk) (S.kind o) hκ l
        exact .inl ⟨l', hl' ▸ hl⟩
      · exact .inr hc

/-- A leaf below a wall of an inlined scope term is a constant. -/
theorem SFlat.wlv_inlC {j : Fin N} : ∀ {w k : Nat}
    (t : SFlat (S.Op ⊕ Fin c) (cAr S c) (cKd S c) w k) (ρw : Fin w → Fin N) (ρk : Fin k → Fin N)
    (ρc : Fin c → Fin N),
    (t.inlC (fun l => .leaf (ρw l)) (fun l => .leaf (ρk l)) (fun l => .leaf (ρc l))).wlv S j = true →
      ∃ l, ρc l = j
  | _, _, .leaf _, _, _, _, h => by simp [SFlat.inlC, Flat.wlv] at h
  | _, _, .node (.inr _) _, _, _, _, h => by simp [SFlat.inlC, Flat.wlv] at h
  | _, _, .node (.inl o) args, ρw, ρk, ρc, h => by
      rcases Flat.wlv_node.mp h with ⟨hκ, p, hp⟩ | ⟨_, p, hp⟩
      · rw [← Kind.envW_comp, ← Kind.envK_comp] at hp
        rcases SFlat.lv_inlC (args p) _ _ ρc hp with ⟨l, _⟩ | ⟨l, _⟩ | hc
        · exact (Kind.w_empty (S.kind o) hκ l).elim
        · exact (Kind.k_empty (S.kind o) hκ l).elim
        · exact hc
      · rw [← Kind.envW_comp, ← Kind.envK_comp] at hp
        exact SFlat.wlv_inlC (args p) _ _ ρc hp

end Leaves

section Rename2
variable {m : Nat}

/-- A leaf of a renamed term is the renamed leaf of the term. -/
theorem Flat.lv_rename (ρ : Fin n → Fin m) {j : Fin m} : ∀ t : Flat S.Op S.Pos n,
    (t.bind fun i => .leaf (ρ i)).lv S j = true → ∃ i, t.lv S i = true ∧ ρ i = j
  | .leaf i, h => ⟨i, by simp [Flat.lv], by simpa [Flat.bind, Flat.lv] using h⟩
  | .node o args, h => by
      obtain ⟨p, hp⟩ := Flat.lv_node.mp h
      obtain ⟨i, hi, hρ⟩ := Flat.lv_rename ρ (args p) hp
      exact ⟨i, Flat.lv_node.mpr ⟨p, hi⟩, hρ⟩

/-- An unguarded leaf of a renamed term is the renamed unguarded leaf of the term. -/
theorem Flat.ulv_rename (ρ : Fin n → Fin m) {j : Fin m} : ∀ t : Flat S.Op S.Pos n,
    (t.bind fun i => .leaf (ρ i)).ulv S j = true → ∃ i, t.ulv S i = true ∧ ρ i = j
  | .leaf i, h => ⟨i, by simp [Flat.ulv], by simpa [Flat.bind, Flat.ulv] using h⟩
  | .node o args, h => by
      obtain ⟨hκ, p, hp⟩ := Flat.ulv_node_iff.mp h
      obtain ⟨i, hi, hρ⟩ := Flat.ulv_rename ρ (args p) hp
      exact ⟨i, Flat.ulv_node_iff.mpr ⟨hκ, p, hi⟩, hρ⟩

/-- A leaf below a wall of a renamed term is the renamed leaf below a wall of the term. -/
theorem Flat.wlv_rename (ρ : Fin n → Fin m) {j : Fin m} : ∀ t : Flat S.Op S.Pos n,
    (t.bind fun i => .leaf (ρ i)).wlv S j = true → ∃ i, t.wlv S i = true ∧ ρ i = j
  | .leaf _, h => by simp [Flat.bind, Flat.wlv] at h
  | .node o args, h => by
      rcases Flat.wlv_node.mp h with ⟨hκ, p, hp⟩ | ⟨hκ, p, hp⟩
      · obtain ⟨i, hi, hρ⟩ := Flat.lv_rename ρ (args p) hp
        exact ⟨i, Flat.wlv_node.mpr (.inl ⟨hκ, p, hi⟩), hρ⟩
      · obtain ⟨i, hi, hρ⟩ := Flat.wlv_rename ρ (args p) hp
        exact ⟨i, Flat.wlv_node.mpr (.inr ⟨hκ, p, hi⟩), hρ⟩

/-- A renaming keeps a leaf. -/
theorem Flat.lv_of_rename (ρ : Fin n → Fin m) {i : Fin n} : ∀ t : Flat S.Op S.Pos n,
    t.lv S i = true → (t.bind fun i => .leaf (ρ i)).lv S (ρ i) = true
  | .leaf i', h => by
      simp only [Flat.lv, decide_eq_true_eq] at h
      subst h; simp [Flat.bind, Flat.lv]
  | .node o args, h => by
      obtain ⟨p, hp⟩ := Flat.lv_node.mp h
      exact Flat.lv_node.mpr ⟨p, Flat.lv_of_rename ρ (args p) hp⟩

/-- A renaming keeps an unguarded leaf. -/
theorem Flat.ulv_of_rename (ρ : Fin n → Fin m) {i : Fin n} : ∀ t : Flat S.Op S.Pos n,
    t.ulv S i = true → (t.bind fun i => .leaf (ρ i)).ulv S (ρ i) = true
  | .leaf i', h => by
      simp only [Flat.ulv, decide_eq_true_eq] at h
      subst h; simp [Flat.bind, Flat.ulv]
  | .node o args, h => by
      obtain ⟨hκ, p, hp⟩ := Flat.ulv_node_iff.mp h
      exact Flat.ulv_node_iff.mpr ⟨hκ, p, Flat.ulv_of_rename ρ (args p) hp⟩

/-- A renaming keeps a leaf below a wall. -/
theorem Flat.wlv_of_rename (ρ : Fin n → Fin m) {i : Fin n} : ∀ t : Flat S.Op S.Pos n,
    t.wlv S i = true → (t.bind fun i => .leaf (ρ i)).wlv S (ρ i) = true
  | .leaf _, h => by simp [Flat.wlv] at h
  | .node o args, h => by
      rcases Flat.wlv_node.mp h with ⟨hκ, p, hp⟩ | ⟨hκ, p, hp⟩
      · exact Flat.wlv_node.mpr (.inl ⟨hκ, p, Flat.lv_of_rename ρ (args p) hp⟩)
      · exact Flat.wlv_node.mpr (.inr ⟨hκ, p, Flat.wlv_of_rename ρ (args p) hp⟩)

end Rename2

/-- An edge from an earlier entry of a DAG of scopes stays among the earlier entries. -/
theorem DSys.reach_castAdd {c n : Nat} (d : DSys S c) (sc : Scope S c n) {j : Fin c}
    {k : Fin (c + n)} (h : Relation.ReflTransGen (REdge (DSys.snoc d sc).graph) (Fin.castAdd n j) k) :
    ∃ k₀, k = Fin.castAdd n k₀ ∧ Relation.ReflTransGen (REdge d.graph) j k₀ := by
  induction h with
  | refl => exact ⟨j, rfl, .refl⟩
  | tail _ he ih =>
    obtain ⟨k₀, rfl, hr⟩ := ih
    simp only [REdge, DSys.graph, Fin.append_left] at he
    obtain ⟨i, hi, hρ⟩ := Flat.lv_rename _ _ he
    exact ⟨i, hρ.symm, hr.tail hi⟩

/-- **The invariant of a DAG of scopes**: an unguarded edge lowers the entry, and everything that a
    leaf below a wall reaches is below the entry. -/
theorem DSys.order : ∀ {N : Nat} (d : DSys S N),
    (∀ i j, (d.graph i).ulv S j = true → j.val < i.val) ∧
    ∀ i j, (d.graph i).wlv S j = true → ∀ k, Relation.ReflTransGen (REdge d.graph) j k → k.val < i.val
  | _, .nil => ⟨fun i => i.elim0, fun i => i.elim0⟩
  | _, .snoc (c := c) (n := n) d sc => by
      obtain ⟨ihu, ihw⟩ := DSys.order d
      refine ⟨fun i j h => ?_, fun i j h k hk => ?_⟩
      · refine Fin.addCases (fun m h => ?_) (fun m h => ?_) i h
        · simp only [DSys.graph, Fin.append_left] at h
          obtain ⟨j₀, hj, rfl⟩ := Flat.ulv_rename _ _ h
          have := ihu m j₀ hj
          simp only [Fin.val_castAdd]; exact this
        · simp only [DSys.graph, Fin.append_right] at h
          rcases SFlat.ulv_inlC (sc m) _ _ _ h with ⟨l, rfl⟩ | ⟨l, rfl⟩
          · simp only [Fin.val_natAdd, Fin.val_castLE]; have := l.isLt; omega
          · simp only [Fin.val_castAdd, Fin.val_natAdd]; have := l.isLt; omega
      · refine Fin.addCases (fun m h hk => ?_) (fun m h hk => ?_) i h hk
        · simp only [DSys.graph, Fin.append_left] at h
          obtain ⟨j₀, hj, rfl⟩ := Flat.wlv_rename _ _ h
          obtain ⟨k₀, rfl, hr⟩ := DSys.reach_castAdd d sc hk
          have := ihw m j₀ hj k₀ hr
          simp only [Fin.val_castAdd]; exact this
        · simp only [DSys.graph, Fin.append_right] at h
          obtain ⟨l, rfl⟩ := SFlat.wlv_inlC (sc m) _ _ _ h
          obtain ⟨k₀, rfl, _⟩ := DSys.reach_castAdd d sc hk
          simp only [Fin.val_castAdd, Fin.val_natAdd]; have := k₀.isLt; omega

/-- **The graph form of a DAG of scopes passes the guard of a DAG of scopes.** -/
theorem DSys.dagGuard {N : Nat} (d : DSys S N) : DagGuard S d.graph := by
  obtain ⟨hu, hw⟩ := DSys.order d
  exact ⟨noCycle_of_rank (fun i => i.val) fun i j h => hu i j h,
    fun i j h hr => absurd (hw i j h i hr) (Nat.lt_irrefl _)⟩

/-- **A renaming keeps the guard of a DAG of scopes**, from the renamed system back to the system. -/
theorem dagGuard_of_rename {sys g : Fin n → Flat S.Op S.Pos n} (π : Equiv.Perm (Fin n))
    (hg : ∀ m, g m = (sys (π.symm m)).bind fun j => .leaf (π j)) (h : DagGuard S g) :
    DagGuard S sys := by
  have hπ : ∀ i, g (π i) = (sys i).bind fun j => .leaf (π j) := fun i => by
    rw [hg, Equiv.symm_apply_apply]
  refine ⟨fun ⟨w, m, hm, hwm, hw⟩ => h.noCycle ⟨fun t => π (w t), m, hm, by simp only [hwm],
    fun t ht => ?_⟩, fun i j hwl hr => h.wall (π i) (π j) ?_ ?_⟩
  · show (g (π (w t))).ulv S (π (w (t + 1))) = true
    rw [hπ]; exact Flat.ulv_of_rename π _ (hw t ht)
  · rw [hπ]; exact Flat.wlv_of_rename π _ hwl
  · have key : ∀ a b, Relation.ReflTransGen (REdge sys) a b →
        Relation.ReflTransGen (REdge g) (π a) (π b) := by
      intro a b hab
      induction hab with
      | refl => exact .refl
      | tail _ he ih =>
        refine ih.tail ?_
        show (g (π _)).lv S (π _) = true
        rw [hπ]; exact Flat.lv_of_rename π _ he
    exact key _ _ hr

end Rename

/-! ## `Compat` and lawfulness at the solution -/

section AtSolution
variable {S : Container} {R : Step S V M}

/-- `Compat` reads two inputs, so codecs that approximate at every depth carry it to the limit. -/
theorem compat_of_approx {V M : Type} {depth : V → Nat} {c d : Codec V M}
    (h : ∀ k, ∃ c' d', AgreeLe depth k c c' ∧ AgreeLe depth k d d' ∧ Compat c' d') : Compat c d := by
  intro a t hp hor
  obtain ⟨c', d', hc, hd, hC⟩ := h (max (depth a) (depth t))
  have e1 : c.p a = c'.p a := hc.f .dual a (le_max_left _ _)
  have e2 : d.p a = d'.p a := hd.f .dual a (le_max_left _ _)
  have e3 : d.e t = d'.e t := hd.f .host t (le_max_right _ _)
  rw [e2]
  rw [e1] at hp
  rw [e2, e3] at hor
  exact hC a t hp hor

/-- **`Compat` reaches the solution**: options with no leaf under a wall that are pairwise
    compatible at every stage of the normal form are pairwise compatible at the solution. -/
theorem compat_strat (hd : ∀ v, 0 < depth v) (hS : R.Lawful depth) (sys : SSys S n)
    {os : List (Flat S.Op S.Pos n)} (hok : ∀ t ∈ os, t.Ok S)
    (hst : ∀ k, ∀ t ∈ os, ∀ t' ∈ os, Compat (t.interp R (sysStage (sysB R (nf S sys)) k))
      (t'.interp R (sysStage (sysB R (nf S sys)) k))) :
    ∀ t ∈ os, ∀ t' ∈ os, Compat (t.interp R (solve depth (sysB R (nf S sys))))
      (t'.interp R (solve depth (sysB R (nf S sys)))) := fun t ht t' ht' =>
  compat_of_approx (depth := depth) fun k =>
    ⟨_, _, Flat.ok_agree hS (solve_agree hd (nf_contractive hS sys) k) t (hok t ht),
      Flat.ok_agree hS (solve_agree hd (nf_contractive hS sys) k) t' (hok t' ht'), hst k t ht t' ht'⟩

/-- **Lawfulness reaches the solution**: lawful stages of the normal form give a lawful solution. -/
theorem lawful_strat (hd : ∀ v, 0 < depth v) (hS : R.Lawful depth) (sys : SSys S n) {member : V → M}
    (hs : ∀ k i, Lawful member (sysStage (sysB R (nf S sys)) k i)) (i : Fin n) :
    Lawful member (solve depth (sysB R (nf S sys)) i) :=
  lawful_solve hd (nf_contractive hS sys) hs i

end AtSolution

/-! ## A leaf below a wall has no stratified form -/

section WallLeaf
variable {S : Container} {R : Step S V M}

/-- A renaming keeps a term with no leaf. -/
theorem Flat.closedB_rename (π : Fin n → Fin n) : ∀ t : Flat S.Op S.Pos n,
    (t.bind fun j => .leaf (π j)).closedB S = t.closedB S
  | .leaf _ => rfl
  | .node o args => by
      simp only [Flat.bind, Flat.closedB]
      congr 1
      funext p
      exact Flat.closedB_rename π (args p)

/-- A renaming keeps a term with no leaf under a wall. -/
theorem Flat.okB_rename (π : Fin n → Fin n) : ∀ t : Flat S.Op S.Pos n,
    (t.bind fun j => .leaf (π j)).okB S = t.okB S
  | .leaf _ => rfl
  | .node o args => by
      simp only [Flat.bind, Flat.okB]
      cases S.kind o <;> simp only [Flat.closedB_rename, Flat.okB_rename]

/-- **A leaf below a wall has no stratified form**: no renaming of a term with a leaf below a wall
    is an entry of the graph form of a stratified system. -/
theorem wall_leaf_no_strat (ssys : SSys S n) (π : Fin n → Fin n) (t : Flat S.Op S.Pos n)
    (ht : t.okB S = false) (m : Fin n) : ssys.graph m ≠ t.bind fun j => .leaf (π j) := by
  intro h
  have hok := ((graphGuard_iff _).mp ssys.graphGuard).1 m
  rw [h, Flat.okB_rename, ht] at hok
  exact nomatch hok

/-- **A renaming keeps the graph guard**, from the renamed system back to the system. -/
theorem graphGuard_of_rename {sys g : Fin n → Flat S.Op S.Pos n} (π : Equiv.Perm (Fin n))
    (hg : ∀ m, g m = (sys (π.symm m)).bind fun j => .leaf (π j)) (h : graphGuard S g = true) :
    graphGuard S sys = true := by
  have hπ : ∀ i, g (π i) = (sys i).bind fun j => .leaf (π j) := fun i => by
    rw [hg, Equiv.symm_apply_apply]
  have hG := (graphGuard_iff g).mp h
  refine (graphGuard_iff sys).mpr ⟨fun i => ?_, fun ⟨w, m, hm, hwm, hw⟩ =>
    hG.2 ⟨fun t => π (w t), m, hm, by simp only [hwm], fun t ht => ?_⟩⟩
  · have hi := hG.1 (π i)
    rwa [hπ, Flat.okB_rename] at hi
  · show (g (π (w t))).ulv S (π (w (t + 1))) = true
    rw [hπ]; exact Flat.ulv_of_rename π _ (hw t ht)

end WallLeaf

/-! ## A wall names a constant -/

section WallConst

/-- A step with one wall of one argument, and one nullary operation. -/
abbrev wStep : Container where
  A := Bool
  B | true => Fin 1 | false => Fin 0
  pos | true => List.finRange 1 | false => List.finRange 0
  pos_complete | true => List.mem_finRange | false => List.mem_finRange
  kind | true => .wall | false => .keep

/-- A wall may name a constant: the second scope's wall names the first scope's entry. -/
def wallConst : DSys wStep 2 :=
  .snoc (c := 1) (n := 1) (.snoc (c := 0) (n := 1) .nil fun _ => .node (.inl false) Fin.elim0)
    fun _ => .node (.inl true) fun _ => .node (.inr ⟨0, by decide⟩) Empty.elim

end WallConst

end Calculus.Alg
