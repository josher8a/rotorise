import Calculus.Lang.ScopeDisjoint

/-!
# Soundness of a closed codec

The judgement `Typed` types a term of a scope. Each operation has one rule, `TOp.rule`, and the
rule answers `none` for a `legacy`, for an object with a `fill`, and for a container without its
former. `Obligations` holds the semantic premises: the cancellation of a `held`, and the pairwise
compatibility of the options of a union.

A closed codec owes the obligations of its scope at each stage of the normal form of the scope,
given that the stage before is lawful. `Closed.sound` proves that a typed closed codec that meets
its obligations is lawful at each entry. Each stage is lawful by the soundness of the terms, and
`lawful_strat` carries the laws to the solution. The proof is structural on the derivation.
-/

namespace Calculus.Alg.Scoped

variable {B : Sig} [Mean B] (τ : (s : Bool) → TableAt B s)

/-- A slot mode is a `fill`. -/
def SlotMode.isFill : SlotMode B → Bool
  | .fill _ => true
  | _ => false

/-- The held set and the member of an operation from its positions, or `none` with no rule. -/
def TOp.rule : (o : TOp B) → (o.Pos → Mean.C B) → (o.Pos → Mean.V (B := B) → Prop) →
    (o.Pos → Option (Mean.Mem (B := B))) →
    Option ((Mean.V (B := B) → Prop) × Option (Mean.Mem (B := B)))
  | .prim g, _, _, _ => some ((Mean.ground g).T, (Mean.ground g).μ)
  | .opaq, _, _, _ => some (fun _ => True, none)
  | .never, _, _, _ => some (HNever, none)
  | .set, _, T, μ => (Mean.set (B := B)).map fun L => (L.held (T ()), (μ ()).bind L.member)
  | .list _ s _, _, T, _ => (Mean.list (B := B)).map fun L =>
      (HList L.p (List.ofFn fun p => T (.inl p)) (optOf s fun p => T (.inr (.inl p)))
        (List.ofFn fun p => T (.inr (.inr p))), some L.μ)
  | .refine p _, _, T, μ => some (fun v => T () v ∧ Mean.eval false p v, μ ())
  | .held s k₀ ks, cod, T, μ => some (fun v =>
      T true ((PairAt.one s ((τ s).word (k₀ :: ks)) false).1 v) ∧
        (false != s || ((cod false).e v).isSome), μ true)
  | .legacy _, _, _, _ => none
  | .obj fs md s, _, T, _ =>
      if (keyPos fs).all (fun x => !(md x).isFill) then
        (Mean.map (B := B)).map fun F =>
          (HObject F.p fs (fun x => ((md x).isReq, T (.inl x))) (optOf s fun p => T (.inr p)),
            some F.μ)
      else none
  | .union _, _, T, μ => some (HUnion (List.ofFn T), unanimous (List.ofFn μ))

section Term

/-- **The judgement** over a term of a scope: an entry reads its held set from its codec. -/
inductive Typed : {w k : Nat} → (Fin w → Mean.C B) → (Fin k → Mean.C B) → Term B w k →
    (Mean.V (B := B) → Prop) → Option (Mean.Mem (B := B)) → Prop where
  | ref {w k : Nat} {ρw : Fin w → Mean.C B} {ρk : Fin k → Mean.C B} (i : Fin k) :
      Typed ρw ρk (.leaf i) (ρk i).T (ρk i).μ
  | node {w k : Nat} {ρw : Fin w → Mean.C B} {ρk : Fin k → Mean.C B} {o : TOp B}
      {args : (p : o.Pos) → Term B ((TOp.kind o).w w) ((TOp.kind o).k w k)}
      {T : o.Pos → Mean.V (B := B) → Prop} {μ : o.Pos → Option (Mean.Mem (B := B))} {r}
      (h : ∀ p, Typed ((TOp.kind o).envW ρw) ((TOp.kind o).envK ρw ρk) (args p) (T p) (μ p))
      (hr : TOp.rule τ o (fun p => SFlat.interp (TStep τ) (args p)
        ((TOp.kind o).envW ρw) ((TOp.kind o).envK ρw ρk)) T μ = some r) :
      Typed ρw ρk (.node o args) r.1 r.2

/-! ## Obligations -/

/-- The obligation of an operation: the cancellation of a `held`, the compatibility of a union. -/
def TOp.obl : (o : TOp B) → (o.Pos → Mean.C B) → Prop
  | .held s k₀ ks, a => Obl1 Mean.mem (a true) s ((τ s).word (k₀ :: ks))
  | .union _, a => ∀ p q, Compat (a p) (a q)
  | _, _ => True

/-- **The obligations of a scope term**: the obligation of each operation, at its positions. -/
def Obligations : {w k : Nat} → (Fin w → Mean.C B) → (Fin k → Mean.C B) → Term B w k → Prop
  | _, _, _, _, .leaf _ => True
  | _, _, ρw, ρk, .node o args =>
      (∀ p, Obligations ((TOp.kind o).envW ρw) ((TOp.kind o).envK ρw ρk) (args p)) ∧
        TOp.obl τ o fun p => SFlat.interp (TStep τ) (args p)
          ((TOp.kind o).envW ρw) ((TOp.kind o).envK ρw ρk)

/-! ## The law of each operation -/

/-- **An operation with a rule keeps the laws**, from lawful positions and its obligation. -/
theorem TOp.lawful {o : TOp B} {a : o.Pos → Mean.C B} {a' : o.Pos → Mean.C B}
    {T : o.Pos → Mean.V (B := B) → Prop} {μ : o.Pos → Option (Mean.Mem (B := B))} {r}
    (hr : TOp.rule τ o a' T μ = some r) (ha : ∀ p, Lawful Mean.mem (a p)) (hob : TOp.obl τ o a) :
    Lawful Mean.mem (TOp.run τ o a) := by
  cases o with
  | prim g => exact Mean.lawful_ground g
  | opaq => exact lawful_idCodec
  | never => exact Lawful.empty
  | set =>
    simp only [TOp.run]
    cases Mean.set (B := B) with
    | none => exact Lawful.empty
    | some L => exact L.lawful (ha ())
  | list n s m =>
    simp only [TOp.run]
    cases Mean.list (B := B) with
    | none => exact Lawful.empty
    | some L =>
      refine lawful_listCodec ?_ ?_ ?_
      · intro c hc; obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hc; exact ha _
      · intro c hc
        match s with
        | ⟨0, _⟩ => exact nomatch hc
        | ⟨1, _⟩ => obtain rfl := Option.some.inj (Option.mem_def.mp hc); exact ha _
      · intro c hc; obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hc; exact ha _
  | refine p pA => exact (ha ()).refine2 _ _
  | held s k₀ ks => exact (ha true).held1 _ hob
  | legacy r => exact nomatch hr
  | obj fs md s =>
    simp only [TOp.rule] at hr
    split at hr
    · next hall =>
      simp only [TOp.run]
      cases Mean.map (B := B) with
      | none => exact Lawful.empty
      | some F =>
        refine lawful_objectCodec (decide_eq_true fun k => ?_) (fun k => ?_) fun c hc => ?_
        · have h := List.all_eq_true.mp hall k (keyPos_complete fs k)
          show (mkField (md k) _).isFill = false
          cases hm : md k <;> simp only [hm, SlotMode.isFill, Bool.not_true] at h <;>
            first | rfl | exact nomatch h
        · show Lawful _ (mkField (md k) _).codec
          cases md k <;> exact ha _
        · match s with
          | ⟨0, _⟩ => exact nomatch hc
          | ⟨1, _⟩ => cases hc; exact ha _
    · exact nomatch hr
  | union m =>
    refine lawful_altCodec (fun c hc => ?_) (fun c hc c' hc' => ?_) fun m' hm c hc t v he => ?_
    · obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hc; exact ha p
    · obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hc
      obtain ⟨q, rfl⟩ := List.mem_ofFn.mp hc'
      exact hob p q
    · obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hc
      exact (ha p).writes (unanimous_spec hm _ (List.mem_ofFn.mpr ⟨p, rfl⟩)) he

/-! ## Soundness -/

/-- **Soundness of a scope term**: a typed term that meets its obligations at lawful codecs is lawful. -/
theorem sound_term {w k : Nat} {ρw' : Fin w → Mean.C B}
    {ρk' : Fin k → Mean.C B} {t : Term B w k} {T μ} (h : Typed τ ρw' ρk' t T μ) :
    ∀ {ρw : Fin w → Mean.C B} {ρk : Fin k → Mean.C B}, (∀ j, Lawful Mean.mem (ρw j)) →
      (∀ j, Lawful Mean.mem (ρk j)) → Obligations τ ρw ρk t →
      Lawful Mean.mem (SFlat.interp (TStep τ) t ρw ρk) := by
  induction h with
  | ref i => exact fun _ hk _ => hk i
  | node _ hr ih =>
    intro ρw ρk hw hk hob
    exact TOp.lawful τ hr (fun p => ih p (Kind.envW_all hw _) (Kind.envK_all hw hk _) (hob.1 p))
      hob.2

end Term

/-! ## A closed codec -/

/-- The stages of the normal form of the scope of a closed codec. -/
abbrev Closed.stage {N : Nat} (d : Closed B N) : Nat → Fin N → Mean.C B :=
  sysStage (sysB (TStep τ) (nf (TSig B) d))

/-- The solution of the scope of a closed codec. -/
abbrev Closed.top {N : Nat} (d : Closed B N) : Fin N → Mean.C B :=
  d.sol (TStep τ) Mean.d

/-- **A typed closed codec**: each entry is typed at the solution of the scope. -/
def Closed.Typed {N : Nat} (d : Closed B N) : Prop :=
  ∀ i, ∃ T μ, Scoped.Typed τ (Closed.top τ d)
    (fun j => Closed.top τ d (Fin.castLE (Nat.le_of_lt i.isLt) j)) (d i) T μ

/-- **The obligations of a closed codec**: each entry meets them at each stage after a lawful stage. -/
def Closed.Obligations {N : Nat} (d : Closed B N) : Prop :=
  ∀ k, (∀ j, Lawful Mean.mem (Closed.stage τ d k j)) →
    ∀ i, Scoped.Obligations τ (Closed.stage τ d k)
      (fun j => Closed.stage τ d (k + 1) (Fin.castLE (Nat.le_of_lt i.isLt) j)) (d i)

/-- **The stages of a typed closed codec are lawful**, where its obligations hold: each stage is
    lawful by the soundness of the terms at the stage before. -/
theorem Closed.stage_lawful {N : Nat} (d : Closed B N) (hty : Closed.Typed τ d)
    (hob : Closed.Obligations τ d) : ∀ k i, Lawful Mean.mem (Closed.stage τ d k i) := by
  intro k
  induction k with
  | zero => exact fun _ => Lawful.empty
  | succ k ih =>
    intro ⟨i, hi⟩
    induction i using Nat.strong_induction_on with
    | _ i ihi =>
      obtain ⟨T, μ, ht⟩ := hty ⟨i, hi⟩
      have e := interp_nf (R := TStep τ) d (Closed.stage τ d k) ⟨i, hi⟩
      exact (congrArg (Lawful Mean.mem) e).mpr <|
        sound_term τ ht ih (fun j => ihi j.val j.isLt _) (hob k ih ⟨i, hi⟩)

/-- **Soundness of a closed codec**: a typed closed codec that meets its obligations is lawful. -/
theorem Closed.sound {N : Nat} (d : Closed B N) (hty : Closed.Typed τ d)
    (hob : Closed.Obligations τ d) : ∀ i, Lawful Mean.mem (d.sol (TStep τ) Mean.d i) :=
  lawful_strat Mean.d_pos (TStep_lawful τ) d
    (Closed.stage_lawful τ d hty hob)

/-- **The meaning of a typed closed codec that meets its obligations is lawful.** -/
theorem Closed.meaning_lawful {N : Nat} (d : Closed B N) (hty : Closed.Typed τ d)
    (hob : Closed.Obligations τ d) (root : Fin N) : Lawful Mean.mem (Closed.meaning τ d root) :=
  Closed.sound τ d hty hob root

/-! ## No rule for a `legacy` or a `fill` -/

/-- A closed codec of one entry: a `legacy` reader over the identity. -/
def legacyClosed (r : B.R) : Closed B 1 :=
  fun i => Term.legacy (w := 1) (k := i) .opaq r

/-- **A closed codec with a `legacy` is not typed**: the rule of `legacy` answers `none`. -/
theorem legacyClosed_untyped (r : B.R) : ¬ Closed.Typed τ (legacyClosed r) := fun h => by
  unfold legacyClosed Closed.Typed at h
  obtain ⟨T, μ, ht⟩ := h 0
  cases ht with
  | node _ hr => exact nomatch hr

/-- A closed codec of one entry: an object with one `fill` slot. -/
def fillClosed (v : B.K) : Closed B 1 :=
  fun i =>
    Term.object (w := 1) (k := i) {"a"} (fun _ => (.fill v, .opaq)) none

/-- **A closed codec with a `fill` is not typed**: the rule of the object answers `none`. -/
theorem fillClosed_untyped (v : B.K) : ¬ Closed.Typed τ (fillClosed v) := fun h => by
  unfold fillClosed Closed.Typed at h
  obtain ⟨T, μ, ht⟩ := h 0
  cases ht with
  | node _ hr =>
    simp only [TOp.rule] at hr
    split at hr
    · next hall =>
      exact nomatch List.all_eq_true.mp hall ⟨"a", List.mem_singleton_self _⟩
        (keyPos_complete _ _)
    · exact nomatch hr

end Calculus.Alg.Scoped
