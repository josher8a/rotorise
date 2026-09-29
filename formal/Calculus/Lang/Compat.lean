import Calculus.Lang.DisjointA

/-!
# The compatibility of two terms

A union is the join of its options. The join of two lawful options exists exactly when the two
are compatible (Lawson: `s ∨ t` exists iff `s ∼ t`), and compatibility of two partial bijections is
two halves of agreement: `s⁻¹t` and `st⁻¹` are idempotents. So the union's one law is one decision,
`Term.compat`, run once per half. The write half (`side = true`) says that two writers of one value
write one attribute. The read half (`side = false`) says that two readers of one attribute read one
value.

Each row of the decision is one of two warrants, per half and per component: the two terms are
**disjoint** there, or both are **bounded** by one codec there. The bottom agrees with every term.
Two held-free terms below the top are bounded by the top. `Term.disjoint` is the disjoint row. A
closed-context oracle of the universe decides orthogonality of each half. A `held` writes inside
its caller outer. It reads inside its inner term where its stored word is empty, and inside its
stored outer otherwise. So a `held` whose half is disjoint from the partner agrees there. Two
`held`s of one adapter agree where their inner terms agree. A
container agrees with a container of its former where the components agree.

The flags: `top` says that both environments are empty, so the oracle applies. `s` says that every
environment entry is below the top, so the held-free row applies. `compat_sound` states agreement
of the denotations over every two environments that the pairing and the flags admit.
`pairwiseCompat_of_compatPair` discharges the union's obligation of two lawful closed options.
-/

namespace Calculus.Alg

variable {S : Syn}

/-- The oracles that a universe supplies: an orthogonality test for each half at the closed
    context, and a test that two adapter words are one word. -/
structure CompatOracle (S : Syn) where
  orthE : Term S → Term S → Bool
  orthP : Term S → Term S → Bool
  same : Word S → Word S → Bool

/-- The row a `held` gives one half: the write half of a `held` sits inside its caller outer.
    The read half sits inside its inner term where the stored word is empty, and inside its
    stored outer otherwise. -/
def heldSide (side : Bool) : Term S → Option (Term S)
  | .held i P PA k kA => some (if side then half2 S.o.c P PA else
      match halfK S.o.s k kA with | [] => i | _ :: _ => half2 S.o.s P PA)
  | _ => none

/-- **The rows that read no structure**: the bottom, two held-free terms below the top, two
    disjoint terms, the closed-context oracle, and a `held` whose half is disjoint from the
    partner. -/
def cbase [Leaf S] (o : CompatOracle S) (side top s : Bool) (x y : Term S) : Bool :=
  x.isNever || y.isNever || (s && !hasHeld x && !hasHeld y) || Term.disjoint pair0 x y ||
    (top && (if side then o.orthE x y else o.orthP x y)) ||
    (match heldSide side x with | some h => Term.disjoint pair0 h y | none => false) ||
    (match heldSide side y with | some h => Term.disjoint pair0 x h | none => false)

mutual
/-- **The rows of the right operand.** The bottom, a union option by option, a refinement
    through its inner term, and a recursive term unfolded with its binder paired with nothing. -/
def cmpR (fam : Pairing → Bool → Bool → Term S → Bool) (p : Pairing) (top s : Bool) :
    Term S → Bool
  | .never => true
  | .union os => fam p top s (.union os) || cmpRL fam p top s os
  | .refine y q qA => fam p top s (.refine y q qA) || cmpR fam p top s y
  | .mu b => fam p top s (.mu b) || cmpR fam (shiftR p) false (s && !hasHeld b) b
  | y => fam p top s y
def cmpRL (fam : Pairing → Bool → Bool → Term S → Bool) (p : Pairing) (top s : Bool) :
    List (Term S) → Bool
  | [] => true
  | y :: ys => cmpR fam p top s y && cmpRL fam p top s ys
end

/-- The term of a slot, whatever its presence. -/
def ObjectSlot.term : ObjectSlot S → Term S
  | .req t | .optional t => t

/-- Every test of the left row against every term of the right row. -/
def allPairs (fs : List (Term S → Bool)) (ys : List (Term S)) : Bool :=
  fs.all fun f => ys.all f

mutual
/-- **The compatibility decision, one half.** Structural on the left operand. -/
def Term.compat [Leaf S] (o : CompatOracle S) (side : Bool) (p : Pairing) (top s : Bool) :
    Term S → Term S → Bool
  | .never, _ => true
  | .refine x q qA, y => cbase o side top s (.refine x q qA) y || Term.compat o side p top s x y
  | .union os, y => cbase o side top s (.union os) y || Term.compatL o side p top s os y
  | .mu b, .mu b' => cbase o side top s (.mu b) (.mu b') ||
      (Term.compat o true (pairMu p) false (s && !hasHeld b && !hasHeld b') b b' &&
        Term.compat o false (pairMu p) false (s && !hasHeld b && !hasHeld b') b b')
  | .mu b, y => cbase o side top s (.mu b) y ||
      Term.compat o side (shiftL p) false (s && !hasHeld b) b y
  | .var i, y => cmpR (fun p' t' s' y' => cbase o side t' s' (.var i) y' ||
      (match y' with | .var j => (p' i j).isSome | _ => false)) p top s y
  | .held i P PA k kA, y => cmpR (fun p' t' s' y' => cbase o side t' s' (.held i P PA k kA) y' ||
      (match y' with
        | .held i' _ _ k' kA' => o.same (halfK S.o.c k kA) (halfK S.o.c k' kA') &&
            decide (halfK S.o.s k kA = halfK S.o.s k' kA') && Term.compat o side p' t' s' i i'
        | _ => false)) p top s y
  | .prim g, y => cmpR (fun _ t' s' y' => cbase o side t' s' (.prim g) y') p top s y
  | .opaq, y => cmpR (fun _ t' s' y' => cbase o side t' s' .opaq y') p top s y
  | .set a, y => cmpR (fun p' t' s' y' => cbase o side t' s' (.set a) y' ||
      (match y' with | .set a' => Term.compat o side p' t' s' a a' | _ => false)) p top s y
  | .list pre sp suf, y => cmpR (fun p' t' s' y' => cbase o side t' s' (.list pre sp suf) y' ||
      (match y' with
        | .list pre' sp' suf' =>
            allPairs (Term.compatTs o side p' t' s' pre ++ Term.compatO o side p' t' s' sp ++
              Term.compatTs o side p' t' s' suf) (pre' ++ sp'.toList ++ suf')
        | _ => false)) p top s y
  | .object (.mk fs f w), y => cmpR (fun p' t' s' y' => cbase o side t' s' (.object (.mk fs f w)) y' ||
      (match y' with
        | .object b' =>
            decide (∀ k : {k // k ∈ fs ∪ b'.fields},
              (if h : k.1 ∈ fs then ObjectSlot.compat o side p' t' s' (f ⟨k.1, h⟩) (b'.slotAt k.1)
               else Term.compatW o side p' t' s' w (b'.slotAt k.1).term) = true) &&
            Term.compatW o side p' t' s' w b'.block
        | _ => false)) p top s y
termination_by structural x _ => x
/-- A union is compatible with the right operand where each option is. -/
def Term.compatL [Leaf S] (o : CompatOracle S) (side : Bool) (p : Pairing) (top s : Bool) :
    List (Term S) → Term S → Bool
  | [], _ => true
  | x :: xs, y => Term.compat o side p top s x y && Term.compatL o side p top s xs y
termination_by structural xs _ => xs
/-- The test at each position of a row, partially applied. -/
def Term.compatTs [Leaf S] (o : CompatOracle S) (side : Bool) (p : Pairing) (top s : Bool) :
    List (Term S) → List (Term S → Bool)
  | [] => []
  | t :: ts => Term.compat o side p top s t :: Term.compatTs o side p top s ts
termination_by structural ts => ts
/-- …at the spread. -/
def Term.compatO [Leaf S] (o : CompatOracle S) (side : Bool) (p : Pairing) (top s : Bool) :
    Option (Term S) → List (Term S → Bool)
  | none => []
  | some t => [Term.compat o side p top s t]
termination_by structural t => t
/-- …at the open block: a closed body holds the bottom there. -/
def Term.compatW [Leaf S] (o : CompatOracle S) (side : Bool) (p : Pairing) (top s : Bool) :
    Option (Term S) → Term S → Bool
  | none, _ => true
  | some t, y => Term.compat o side p top s t y
termination_by structural t => t
/-- Two slots at one name: the terms, whatever the presence. -/
def ObjectSlot.compat [Leaf S] (o : CompatOracle S) (side : Bool) (p : Pairing) (top s : Bool) :
    ObjectSlot S → ObjectSlot S → Bool
  | .req x, y => Term.compat o side p top s x y.term
  | .optional x, y => Term.compat o side p top s x y.term
termination_by structural f _ => f
end

/-- **The decision at two closed options**: both halves. -/
def compatPair [Leaf S] (o : CompatOracle S) (x y : Term S) : Bool :=
  Term.compat o true pair0 true true x y && Term.compat o false pair0 true true x y


/-- **Agreement on one half of a universe**: the write half (`side = true`) is agreement at the
    orientation of the universe, and the read half is agreement at the dual orientation. -/
abbrev AgreeHalf (S : Syn) {V A M : Type} (side : Bool) (c d : Codec V A M) : Prop :=
  Agree (bif side then S.o else S.o.op) c d

section Sound
variable [Sem S] {α : Table S} {β : Table S.op}

/-- The denotation of the half of two outers is the half of the two denotations. -/
theorem denote_half2 (s : Bool) (P PA : Term S) (ρ : List S.C) :
    denote α β (half2 s P PA) ρ = half2 s (denote α β P ρ) (denote α β PA ρ) :=
  half2_apply (denote α β · ρ) s P PA

/-- **What the flags and the pairing promise of the two environments.** A paired binder pair
    agrees on both halves. Under `s`, every entry is below the top. Under `top`, both
    environments are empty. -/
structure CEnv (p : Pairing) (top s : Bool) (ρ ρ' : List S.C) : Prop where
  pair : ∀ i j k, p i j = some k → ∀ o, Agree o (envAt ρ i) (envAt ρ' j)
  safeL : s = true → ∀ i, Sub (envAt ρ i) (Syn.top (S := S))
  safeR : s = true → ∀ i, Sub (envAt ρ' i) (Syn.top (S := S))
  top : top = true → ρ = [] ∧ ρ' = []

/-- What the oracles promise, at every table. Two words that the adapter test calls one are
    one word, so a table gives them one pair. -/
structure OracleSound (o : CompatOracle S) : Prop where
  e : ∀ {α : Table S} {β : Table S.op} x y, o.orthE x y = true → ∀ v,
    (((denote α β x []).f S.o v).isSome && ((denote α β y []).f S.o v).isSome) = false
  p : ∀ {α : Table S} {β : Table S.op} x y, o.orthP x y = true → ∀ a,
    (((denote α β x []).f S.o.op a).isSome && ((denote α β y []).f S.o.op a).isSome) = false
  same : ∀ k k', o.same k k' = true → k = k'

/-- The stages of a held-free body over an environment below the top are below the top. -/
theorem stage_sub [TopLaws S] {b : Term S} (hb : hasHeld b = false) {ρ : List S.C}
    (henv : ∀ i, Sub (envAt ρ i) (Syn.top (S := S))) :
    ∀ n, Sub (muStage (fun c => denote α β b (c :: ρ)) n) (Syn.top (S := S))
  | 0 => sub_empty
  | n + 1 => sub_denoteIn b hb (_ :: ρ) fun i => match i with
      | 0 => stage_sub hb henv n
      | i + 1 => henv i

/-- An unfolding of the left operand keeps the promise: the new left binder pairs with nothing. -/
theorem CEnv.left {p : Pairing} {top s s' : Bool} {ρ ρ' : List S.C} (he : CEnv p top s ρ ρ')
    (c : S.C) (hs : s' = true → s = true) (hc : s' = true → Sub c (Syn.top (S := S))) :
    CEnv (shiftL p) false s' (c :: ρ) ρ' where
  pair i j k h o := match i, h with
    | i + 1, h => he.pair i j k h o
  safeL h i := match i with
    | 0 => hc h
    | i + 1 => he.safeL (hs h) i
  safeR h := he.safeR (hs h)
  top h := nomatch h

/-- …and an unfolding of the right operand. -/
theorem CEnv.right {p : Pairing} {top s s' : Bool} {ρ ρ' : List S.C} (he : CEnv p top s ρ ρ')
    (c : S.C) (hs : s' = true → s = true) (hc : s' = true → Sub c (Syn.top (S := S))) :
    CEnv (shiftR p) false s' ρ (c :: ρ') where
  pair i j k h o := match j, h with
    | j + 1, h => he.pair i j k h o
  safeL h := he.safeL (hs h)
  safeR h i := match i with
    | 0 => hc h
    | i + 1 => he.safeR (hs h) i
  top h := nomatch h

/-- Two binders unfolded together keep the promise where their stages agree on both halves. -/
theorem CEnv.mu {p : Pairing} {top s s' : Bool} {ρ ρ' : List S.C} (he : CEnv p top s ρ ρ')
    (c c' : S.C) (hcc : ∀ o, Agree o c c') (hs : s' = true → s = true)
    (hc : s' = true → Sub c (Syn.top (S := S))) (hc' : s' = true → Sub c' (Syn.top (S := S))) :
    CEnv (pairMu p) false s' (c :: ρ) (c' :: ρ') where
  pair i j k h o := match i, j, h with
    | 0, 0, _ => hcc o
    | i + 1, j + 1, h => by
        simp only [pairMu, Option.map_eq_some_iff] at h
        obtain ⟨k', hk', -⟩ := h
        exact he.pair i j k' hk' o
  safeL h i := match i with
    | 0 => hc h
    | i + 1 => he.safeL (hs h) i
  safeR h i := match i with
    | 0 => hc' h
    | i + 1 => he.safeR (hs h) i
  top h := nomatch h

/-- A disjoint pair has apart write domains, over every two environments. -/
theorem disjoint_domE [PrimAdm S] [Leaf S] [LeafAdm S] [LeafMeet S] [FormerAdm S] [Shapes S]
    [TopLaws S] {x y : Term S} (h : Term.disjoint pair0 x y = true) (ρ ρ' : List S.C) (v : S.V) :
    (((denote α β x ρ).f S.o v).isSome && ((denote α β y ρ').f S.o v).isSome) = false := by
  have := disjoint_sound (α := α) (β := β) pair0 x y h ρ ρ' (fun _ _ _ hp => nomatch hp) v
  rwa [Adm_eq_isSome, Adm_eq_isSome] at this

/-- …and apart read domains. -/
theorem disjoint_domP [PrimAdmA S] [Leaf S] [LeafMeet S] [LeafAdmA S] [FormerAdmA S] [Shapes S]
    [TopLaws S] {x y : Term S} (h : Term.disjoint pair0 x y = true) (ρ ρ' : List S.C) (a : Syn.A S) :
    (((denote α β x ρ).f S.o.op a).isSome && ((denote α β y ρ').f S.o.op a).isSome) = false := by
  have := disjoint_soundA (α := α) (β := β) pair0 x y h ρ ρ' (fun _ _ _ hp => nomatch hp) a
  rwa [AdmA_eq_isSome, AdmA_eq_isSome] at this

/-- Apartness moves to a codec whose domain lies inside. -/
theorem apart_of_imp {x x' y : Bool} (h : x = true → x' = true) (h' : (x' && y) = false) :
    (x && y) = false := by
  cases x <;> cases y <;> simp_all

/-- …on the right. -/
theorem apart_of_imp' {x y y' : Bool} (h : y = true → y' = true) (h' : (x && y') = false) :
    (x && y) = false := by
  cases x <;> cases y <;> simp_all

/-- A `held` acts at an orientation only where the outer of the caller side of the orientation
    acts. -/
theorem held_dom_outer {i P PA : Term S} {k : List (S.sig.G false × Bool)}
    {kA : List (S.sig.G true × Bool)} {ρ : List S.C} (o : Orient) (x : Mean.Car (B := S.sig) o.c)
    (h : ((denote α β (.held i P PA k kA) ρ).f o x).isSome = true) :
    ((denote α β (half2 o.c P PA) ρ).f o x).isSome = true := by
  have h' : ((held2 (denote α β i ρ) (denote α β P ρ) (denote α β PA ρ)
      ((tables S.o α β false).word k).1 ((tables S.o α β false).word k).2
      ((tables S.o α β true).word kA).1 ((tables S.o α β true).word kA).2).f o x).isSome = true := h
  rw [held2_f_isSome, Bool.and_eq_true] at h'
  rw [denote_half2, half2_f, half2_apply Option.isSome]
  exact h'.1

/-- …and, where the word of the caller side of the orientation is empty, only where the inner
    term acts. -/
theorem held_dom_inner {i P PA : Term S} {k : List (S.sig.G false × Bool)}
    {kA : List (S.sig.G true × Bool)} {ρ : List S.C} (o : Orient) (x : Mean.Car (B := S.sig) o.c)
    (hk : halfK o.c k kA = [])
    (h : ((denote α β (.held i P PA k kA) ρ).f o x).isSome = true) :
    ((denote α β i ρ).f o x).isSome = true := by
  have h' : ((held2 (denote α β i ρ) (denote α β P ρ) (denote α β PA ρ)
      ((tables S.o α β false).word k).1 ((tables S.o α β false).word k).2
      ((tables S.o α β true).word kA).1 ((tables S.o α β true).word kA).2).f o x).isSome = true := h
  rw [held2_f_isSome, Bool.and_eq_true, hk] at h'
  exact gate_isSome h'.2

/-- **The rows that read no structure are sound.** -/
theorem cbase_sound [PrimAdm S] [PrimAdmA S] [Leaf S] [LeafAdm S] [LeafMeet S] [FormerAdm S]
    [LeafAdmA S] [FormerAdmA S] [Shapes S] [TopLaws S] {o : CompatOracle S} (ho : OracleSound o) {side top s : Bool}
    {x y : Term S} (h : cbase o side top s x y = true) {p : Pairing} {ρ ρ' : List S.C}
    (he : CEnv p top s ρ ρ') : AgreeHalf S side (denote α β x ρ) (denote α β y ρ') := by
  simp only [cbase, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with ((((((hx | hy) | ⟨⟨hs, hx⟩, hy⟩) | hd) | ⟨ht, ho'⟩) | hl) | hr)
  · cases x <;> simp only [Term.isNever, reduceCtorEq] at hx
    exact agree_empty_left _ _
  · cases y <;> simp only [Term.isNever, reduceCtorEq] at hy
    exact agree_empty_right _ _
  · exact agree_bound (sub_denoteIn x hx ρ (he.safeL hs)) (sub_denoteIn y hy ρ' (he.safeR hs))
  · cases side
    · exact agree_apart (disjoint_domP hd ρ ρ')
    · exact agree_apart (disjoint_domE hd ρ ρ')
  · obtain ⟨rfl, rfl⟩ := he.top ht
    cases side
    · exact agree_apart (ho.p x y ho')
    · exact agree_apart (ho.e x y ho')
  · cases x <;> simp only [heldSide, reduceCtorEq] at hl
    rename_i i P PA k kA
    cases side
    · simp only [Bool.false_eq_true, ite_false] at hl
      revert hl
      cases hk : halfK S.o.s k kA with
      | nil =>
        intro hl
        exact agree_apart fun a =>
          apart_of_imp (held_dom_inner S.o.op a hk) (disjoint_domP hl ρ ρ' a)
      | cons _ _ =>
        intro hl
        exact agree_apart fun a => apart_of_imp (held_dom_outer S.o.op a) (disjoint_domP hl ρ ρ' a)
    · simp only [ite_true] at hl
      exact agree_apart fun v => apart_of_imp (held_dom_outer S.o v) (disjoint_domE hl ρ ρ' v)
  · cases y <;> simp only [heldSide, reduceCtorEq] at hr
    rename_i i P PA k kA
    cases side
    · simp only [Bool.false_eq_true, ite_false] at hr
      revert hr
      cases hk : halfK S.o.s k kA with
      | nil =>
        intro hr
        exact agree_apart fun a =>
          apart_of_imp' (held_dom_inner S.o.op a hk) (disjoint_domP hr ρ ρ' a)
      | cons _ _ =>
        intro hr
        exact agree_apart fun a =>
          apart_of_imp' (held_dom_outer S.o.op a) (disjoint_domP hr ρ ρ' a)
    · simp only [ite_true] at hr
      exact agree_apart fun v => apart_of_imp' (held_dom_outer S.o v) (disjoint_domE hr ρ ρ' v)


mutual
/-- **The rows of the right operand are sound**, for a left codec that the family is sound for. -/
theorem cmpR_sound [TopLaws S] {side : Bool} {X : S.C} {ρ : List S.C}
    {fam : Pairing → Bool → Bool → Term S → Bool}
    (hfam : ∀ p' t' s' y' ρ', fam p' t' s' y' = true → CEnv p' t' s' ρ ρ' →
      AgreeHalf S side X (denote α β y' ρ')) :
    ∀ (y : Term S) (p : Pairing) (top s : Bool) (ρ' : List S.C), cmpR fam p top s y = true →
      CEnv p top s ρ ρ' → AgreeHalf S side X (denote α β y ρ')
  | .never, _, _, _, _, _, _ => agree_empty_right _ X
  | .union os, p, top, s, ρ', h, he => by
      simp only [cmpR, Bool.or_eq_true] at h
      rcases h with h | h
      · exact hfam _ _ _ _ _ h he
      · simp only [denote, denoteAbs]
        exact agree_alt_right (cmpRL_sound hfam os p top s ρ' h he)
  | .refine y q _, p, top, s, ρ', h, he => by
      simp only [cmpR, Bool.or_eq_true] at h
      rcases h with h | h
      · exact hfam _ _ _ _ _ h he
      · simp only [denote, denoteAbs]
        exact agree_sub_right (sub_refine2_self _ _ _) (cmpR_sound hfam y p top s ρ' h he)
  | .mu b, p, top, s, ρ', h, he => by
      simp only [cmpR, Bool.or_eq_true] at h
      rcases h with h | h
      · exact hfam _ _ _ _ _ h he
      · simp only [denote, denoteAbs]
        refine agree_mu_right fun n => ?_
        cases n with
        | zero => exact agree_empty_right _ X
        | succ n =>
          exact cmpR_sound hfam b (shiftR p) false (s && !hasHeld b) (_ :: ρ') h
            (he.right _ (fun hs => by simp only [Bool.and_eq_true] at hs; exact hs.1)
              (fun hs => by
                simp only [Bool.and_eq_true, Bool.not_eq_true'] at hs
                exact stage_sub hs.2 (he.safeR hs.1) n))
  | .prim _, _, _, _, _, h, he => hfam _ _ _ _ _ h he
  | .set _, _, _, _, _, h, he => hfam _ _ _ _ _ h he
  | .list _ _ _, _, _, _, _, h, he => hfam _ _ _ _ _ h he
  | .held _ _ _ _ _, _, _, _, _, h, he => hfam _ _ _ _ _ h he
  | .opaq, _, _, _, _, h, he => hfam _ _ _ _ _ h he
  | .object _, _, _, _, _, h, he => hfam _ _ _ _ _ h he
  | .var _, _, _, _, _, h, he => hfam _ _ _ _ _ h he
/-- …and option by option. -/
theorem cmpRL_sound [TopLaws S] {side : Bool} {X : S.C} {ρ : List S.C}
    {fam : Pairing → Bool → Bool → Term S → Bool}
    (hfam : ∀ p' t' s' y' ρ', fam p' t' s' y' = true → CEnv p' t' s' ρ ρ' →
      AgreeHalf S side X (denote α β y' ρ')) :
    ∀ (ys : List (Term S)) (p : Pairing) (top s : Bool) (ρ' : List S.C),
      cmpRL fam p top s ys = true → CEnv p top s ρ ρ' → ∀ o ∈ denoteList α β ys ρ', AgreeHalf S side X o
  | [], _, _, _, _, _, _ => fun _ h => nomatch h
  | y :: ys, p, top, s, ρ', h, he => by
      simp only [cmpRL, Bool.and_eq_true] at h
      intro o ho
      simp only [denoteList_cons, List.mem_cons] at ho
      rcases ho with rfl | ho
      · exact cmpR_sound hfam y p top s ρ' h.1 he
      · exact cmpRL_sound hfam ys p top s ρ' h.2 he o ho
end

/-- The codec of a slot is the denotation of its term, whatever its presence. -/
theorem fieldSem_codec (f : ObjectSlot S) (ρ : List S.C) : (fieldSem α β f ρ).codec = denote α β f.term ρ := by
  cases f <;> rfl

/-- The codec one name of a body goes through: a declared slot's, or the open block's. -/
theorem entry_cases {fs : Finset String} {f : {k // k ∈ fs} → ObjectSlot S}
    {w : Option (Term S)} {ρ : List S.C} {k : String} {c : S.C}
    (h : entryCodec ⟨fs, fun k => fieldSem α β (f k) ρ⟩ (rcOf (wildSem α β w ρ)) k = some c) :
    (∃ hk : k ∈ fs, c = denote α β (f ⟨k, hk⟩).term ρ) ∨ (k ∉ fs ∧ rcOf (wildSem α β w ρ) = some c) := by
  unfold entryCodec MapOf.at at h
  rcases Decidable.em (k ∈ fs) with hk | hk
  · rw [dif_pos hk] at h
    simp only [Option.some.injEq] at h
    exact Or.inl ⟨hk, by rw [← h, fieldSem_codec]⟩
  · rw [dif_neg hk] at h
    exact Or.inr ⟨hk, h⟩

/-- The codec of the open block is the denotation of the block term. -/
theorem rcOf_wild {w : Option (Term S)} {ρ : List S.C} {c : S.C}
    (h : rcOf (wildSem α β w ρ) = some c) : ∃ t, w = some t ∧ c = denote α β t ρ := by
  cases w with
  | none => exact nomatch h
  | some t => exact ⟨t, rfl, (Option.some.inj h).symm⟩

mutual
/-- **Soundness of the compatibility decision.** Where the decision answers `true` for one half,
    the two denotations agree on that half, over every two environments that the pairing and
    the flags admit. -/
theorem compat_sound [PrimAdm S] [PrimAdmA S] [Leaf S] [LeafAdm S] [LeafMeet S] [FormerAdm S]
    [LeafAdmA S] [FormerAdmA S] [Shapes S] [TopLaws S] {o : CompatOracle S} (ho : OracleSound o) :
    ∀ (x : Term S) (side : Bool) (p : Pairing) (top s : Bool) (y : Term S) (ρ ρ' : List S.C),
      Term.compat o side p top s x y = true → CEnv p top s ρ ρ' →
        AgreeHalf S side (denote α β x ρ) (denote α β y ρ')
  | .never, side, _, _, _, _, _, _, _, _ => agree_empty_left _ _
  | .refine x q _, side, p, top, s, y, ρ, ρ', h, he => by
      simp only [Term.compat, Bool.or_eq_true] at h
      rcases h with h | h
      · exact cbase_sound ho h he
      · simp only [denote, denoteAbs]
        exact agree_sub_left (sub_refine2_self _ _ _) (compat_sound ho x side p top s y ρ ρ' h he)
  | .union os, side, p, top, s, y, ρ, ρ', h, he => by
      simp only [Term.compat, Bool.or_eq_true] at h
      rcases h with h | h
      · exact cbase_sound ho h he
      · simp only [denote, denoteAbs]
        exact agree_alt_left (compatL_sound ho os side p top s y ρ ρ' h he)
  | .mu b, side, p, top, s, y, ρ, ρ', h, he => by
      cases y with
      | mu b' =>
        simp only [Term.compat, Bool.or_eq_true, Bool.and_eq_true] at h
        rcases h with h | ⟨hE, hP⟩
        · exact cbase_sound ho h he
        · have hs : ∀ n, (∀ o, Agree o (muStage (fun c => denote α β b (c :: ρ)) n)
              (muStage (fun c => denote α β b' (c :: ρ')) n)) := by
            intro n
            induction n with
            | zero => exact fun o => agree_empty_left _ _
            | succ n ih =>
              have he' := he.mu (s' := s && !hasHeld b && !hasHeld b') _ _ ih
                (fun hs => by simp only [Bool.and_eq_true] at hs; exact hs.1.1)
                (fun hs => by
                  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hs
                  exact stage_sub hs.1.2 (he.safeL hs.1.1) n)
                (fun hs => by
                  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hs
                  exact stage_sub hs.2 (he.safeR hs.1.1) n)
              exact agree_all (compat_sound ho b true _ _ _ b' _ _ hE he')
                (compat_sound ho b false _ _ _ b' _ _ hP he')
          simp only [denote, denoteAbs]
          exact agree_mu fun n => hs n _
      | _ =>
        simp only [Term.compat, Bool.or_eq_true] at h
        rcases h with h | h
        · exact cbase_sound ho h he
        · simp only [denote, denoteAbs]
          refine agree_mu_left fun n => ?_
          cases n with
          | zero => exact agree_empty_left _ _
          | succ n =>
            refine compat_sound ho b side (shiftL p) false (s && !hasHeld b) _ _ ρ' h
              (he.left _ (fun hs => by simp only [Bool.and_eq_true] at hs; exact hs.1)
                (fun hs => by
                  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hs
                  exact stage_sub hs.2 (he.safeL hs.1) n))
  | .var i, side, p, top, s, y, ρ, ρ', h, he => by
      simp only [Term.compat] at h
      refine cmpR_sound (fun p' t' s' y' ρ'' hf he' => ?_) y p top s ρ' h he
      simp only [Bool.or_eq_true] at hf
      rcases hf with hf | hf
      · exact cbase_sound ho hf he'
      · cases y' <;> simp only [reduceCtorEq] at hf
        rename_i j
        obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hf
        exact he'.pair i j k hk _
  | .held i P _ k _, side, p, top, s, y, ρ, ρ', h, he => by
      simp only [Term.compat] at h
      refine cmpR_sound (fun p' t' s' y' ρ'' hf he' => ?_) y p top s ρ' h he
      simp only [Bool.or_eq_true] at hf
      rcases hf with hf | hf
      · exact cbase_sound ho hf he'
      · cases y' <;> simp only [reduceCtorEq] at hf
        rename_i i' P' PA' k' kA'
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
        obtain ⟨⟨h1, h2⟩, h3⟩ := hf
        obtain ⟨rfl, rfl⟩ := halfK_eq S.o (ho.same _ _ h1) h2
        exact agree_of_agreeS (fun _ => agreeS_held2) _ (compat_sound ho i side p' t' s' i' ρ ρ'' h3 he')
  | .prim g, side, p, top, s, y, ρ, ρ', h, he => by
      simp only [Term.compat] at h
      exact cmpR_sound (fun p' t' s' y' ρ'' hf he' => cbase_sound ho hf he') y p top s ρ' h he
  | .opaq, side, p, top, s, y, ρ, ρ', h, he => by
      simp only [Term.compat] at h
      exact cmpR_sound (fun p' t' s' y' ρ'' hf he' => cbase_sound ho hf he') y p top s ρ' h he
  | .set a, side, p, top, s, y, ρ, ρ', h, he => by
      simp only [Term.compat] at h
      refine cmpR_sound (fun p' t' s' y' ρ'' hf he' => ?_) y p top s ρ' h he
      simp only [Bool.or_eq_true] at hf
      rcases hf with hf | hf
      · exact cbase_sound ho hf he'
      · cases y' <;> simp only [reduceCtorEq] at hf
        rename_i a'
        have ih := compat_sound ho a side p' t' s' a' ρ ρ'' hf he'
        simp only [denote, denoteAbs]
        cases Mean.set (B := S.sig) with
        | none => exact agree_empty_left _ _
        | some L => exact agree_of_agreeS (fun _ => L.agreeS) _ ih
  | .list pre sp suf, side, p, top, s, y, ρ, ρ', h, he => by
      simp only [Term.compat] at h
      refine cmpR_sound (fun p' t' s' y' ρ'' hf he' => ?_) y p top s ρ' h he
      simp only [Bool.or_eq_true] at hf
      rcases hf with hf | hf
      · exact cbase_sound ho hf he'
      · cases y' <;> simp only [reduceCtorEq] at hf
        rename_i pre' sp' suf'
        simp only [allPairs, List.all_eq_true] at hf
        have hr : ∀ d, (d ∈ denoteList α β pre' ρ'' ∨ denoteOpt α β sp' ρ'' = some d ∨
            d ∈ denoteList α β suf' ρ'') → ∃ y ∈ pre' ++ sp'.toList ++ suf', d = denote α β y ρ'' := by
          intro d hd
          rcases hd with hd | hd | hd
          · rw [denoteList_eq] at hd
            obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hd
            exact ⟨y, by simp [hy], rfl⟩
          · cases sp' with
            | none => exact nomatch hd
            | some y =>
              simp only [denoteOpt_some, Option.some.injEq] at hd
              exact ⟨y, by simp, hd.symm⟩
          · rw [denoteList_eq] at hd
            obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hd
            exact ⟨y, by simp [hy], rfl⟩
        have hall : ∀ y ∈ pre' ++ sp'.toList ++ suf', ∀ f ∈ Term.compatTs o side p' t' s' pre ++
            Term.compatO o side p' t' s' sp ++ Term.compatTs o side p' t' s' suf, f y = true :=
          fun y hy f hf' => hf f hf' y hy
        have hpre := compatTs_sound ho pre side p' t' s' ρ ρ'' _
          (fun f hf' y hy => hall y hy f (by simp [hf'])) he'
        have hsp := compatO_sound ho sp side p' t' s' ρ ρ'' _
          (fun f hf' y hy => hall y hy f (by simp [hf'])) he'
        have hsuf := compatTs_sound ho suf side p' t' s' ρ ρ'' _
          (fun f hf' y hy => hall y hy f (by simp [hf'])) he'
        simp only [denote, denoteAbs]
        cases Mean.list (B := S.sig) with
        | none => exact agree_empty_left _ _
        | some L =>
          refine agree_list fun c hc d hd => ?_
          obtain ⟨y, hy, rfl⟩ := hr d hd
          rcases hc with hc | hc | hc
          · exact hpre c hc y hy
          · exact hsp c hc y hy
          · exact hsuf c hc y hy
  | .object (.mk fs f w), side, p, top, s, y, ρ, ρ', h, he => by
      simp only [Term.compat] at h
      refine cmpR_sound (fun p' t' s' y' ρ'' hf he' => ?_) y p top s ρ' h he
      simp only [Bool.or_eq_true] at hf
      rcases hf with hf | hf
      · exact cbase_sound ho hf he'
      · cases y' <;> simp only [reduceCtorEq] at hf
        rename_i b'
        cases b' with
        | mk fs' f' w' =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
        obtain ⟨hall, hw⟩ := hf
        simp only [denote, denoteAbs, bodySemAbs]
        cases Mean.map (B := S.sig) with
        | none => exact agree_empty_left _ _
        | some F =>
          refine agree_object fun k c₁ c₂ h1 h2 => ?_
          rcases entry_cases h1 with ⟨hk, rfl⟩ | ⟨hk, hc₁⟩ <;>
            rcases entry_cases h2 with ⟨hk', rfl⟩ | ⟨hk', hc₂⟩
          · have := hall ⟨k, Finset.mem_union.mpr (Or.inl hk)⟩
            simp only [dif_pos hk] at this
            have hs := cslot_sound ho (f ⟨k, hk⟩) side p' t' s' _ ρ ρ'' this he'
            rw [fieldSem_codec, Body.slotAt_pos hk'] at hs
            exact hs
          · have := hall ⟨k, Finset.mem_union.mpr (Or.inl hk)⟩
            simp only [dif_pos hk] at this
            have hs := cslot_sound ho (f ⟨k, hk⟩) side p' t' s' _ ρ ρ'' this he'
            rw [fieldSem_codec, Body.slotAt_neg hk'] at hs
            obtain ⟨u', rfl, rfl⟩ := rcOf_wild (α := α) (β := β) hc₂
            exact hs
          · have := hall ⟨k, Finset.mem_union.mpr (Or.inr hk')⟩
            simp only [dif_neg hk] at this
            have hs := compatW_sound ho w side p' t' s' _ ρ ρ'' this he' c₁ hc₁
            rw [Body.slotAt_pos hk'] at hs
            exact hs
          · obtain ⟨u', rfl, rfl⟩ := rcOf_wild (α := α) (β := β) hc₂
            exact compatW_sound ho w side p' t' s' _ ρ ρ'' hw he' c₁ hc₁
termination_by structural x => x
/-- …option by option. -/
theorem compatL_sound [PrimAdm S] [PrimAdmA S] [Leaf S] [LeafAdm S] [LeafMeet S] [FormerAdm S]
    [LeafAdmA S] [FormerAdmA S] [Shapes S] [TopLaws S] {o : CompatOracle S} (ho : OracleSound o) :
    ∀ (xs : List (Term S)) (side : Bool) (p : Pairing) (top s : Bool) (y : Term S)
      (ρ ρ' : List S.C), Term.compatL o side p top s xs y = true → CEnv p top s ρ ρ' →
        ∀ c ∈ denoteList α β xs ρ, AgreeHalf S side c (denote α β y ρ')
  | [], _, _, _, _, _, _, _, _, _ => fun _ h => nomatch h
  | x :: xs, side, p, top, s, y, ρ, ρ', h, he => by
      simp only [Term.compatL, Bool.and_eq_true] at h
      intro c hc
      simp only [denoteList_cons, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact compat_sound ho x side p top s y ρ ρ' h.1 he
      · exact compatL_sound ho xs side p top s y ρ ρ' h.2 he c hc
termination_by structural xs => xs
/-- …position by position. -/
theorem compatTs_sound [PrimAdm S] [PrimAdmA S] [Leaf S] [LeafAdm S] [LeafMeet S] [FormerAdm S]
    [LeafAdmA S] [FormerAdmA S] [Shapes S] [TopLaws S] {o : CompatOracle S} (ho : OracleSound o) :
    ∀ (ts : List (Term S)) (side : Bool) (p : Pairing) (top s : Bool) (ρ ρ' : List S.C)
      (ys : List (Term S)), (∀ f ∈ Term.compatTs o side p top s ts, ∀ y ∈ ys, f y = true) →
        CEnv p top s ρ ρ' → ∀ c ∈ denoteList α β ts ρ, ∀ y ∈ ys, AgreeHalf S side c (denote α β y ρ')
  | [], _, _, _, _, _, _, _, _, _ => fun _ h => nomatch h
  | t :: ts, side, p, top, s, ρ, ρ', ys, h, he => by
      intro c hc y hy
      simp only [denoteList_cons, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact compat_sound ho t side p top s y ρ ρ'
          (h _ (by simp [Term.compatTs]) y hy) he
      · exact compatTs_sound ho ts side p top s ρ ρ' ys
          (fun f hf y hy => h f (by simp [Term.compatTs, hf]) y hy) he c hc y hy
termination_by structural ts => ts
/-- …at the spread. -/
theorem compatO_sound [PrimAdm S] [PrimAdmA S] [Leaf S] [LeafAdm S] [LeafMeet S] [FormerAdm S]
    [LeafAdmA S] [FormerAdmA S] [Shapes S] [TopLaws S] {o : CompatOracle S} (ho : OracleSound o) :
    ∀ (t? : Option (Term S)) (side : Bool) (p : Pairing) (top s : Bool) (ρ ρ' : List S.C)
      (ys : List (Term S)), (∀ f ∈ Term.compatO o side p top s t?, ∀ y ∈ ys, f y = true) →
        CEnv p top s ρ ρ' → ∀ c, denoteOpt α β t? ρ = some c → ∀ y ∈ ys, AgreeHalf S side c (denote α β y ρ')
  | none, _, _, _, _, _, _, _, _, _ => fun _ h => nomatch h
  | some t, side, p, top, s, ρ, ρ', ys, h, he => by
      intro c hc y hy
      simp only [denoteOpt_some, Option.some.injEq] at hc
      subst hc
      exact compat_sound ho t side p top s y ρ ρ' (h _ (by simp [Term.compatO]) y hy) he
termination_by structural t? => t?
/-- …at the open block. -/
theorem compatW_sound [PrimAdm S] [PrimAdmA S] [Leaf S] [LeafAdm S] [LeafMeet S] [FormerAdm S]
    [LeafAdmA S] [FormerAdmA S] [Shapes S] [TopLaws S] {o : CompatOracle S} (ho : OracleSound o) :
    ∀ (w : Option (Term S)) (side : Bool) (p : Pairing) (top s : Bool) (y : Term S)
      (ρ ρ' : List S.C), Term.compatW o side p top s w y = true → CEnv p top s ρ ρ' →
        ∀ c, rcOf (wildSem α β w ρ) = some c → AgreeHalf S side c (denote α β y ρ')
  | none, _, _, _, _, _, _, _, _, _ => fun _ h => nomatch h
  | some t, side, p, top, s, y, ρ, ρ', h, he => by
      intro c hc
      simp only [wildSem, wildSemAbs, rcOf, Option.some.injEq] at hc
      subst hc
      exact compat_sound ho t side p top s y ρ ρ' h he
termination_by structural w => w
/-- …at one name. -/
theorem cslot_sound [PrimAdm S] [PrimAdmA S] [Leaf S] [LeafAdm S] [LeafMeet S] [FormerAdm S]
    [LeafAdmA S] [FormerAdmA S] [Shapes S] [TopLaws S] {o : CompatOracle S} (ho : OracleSound o) :
    ∀ (f : ObjectSlot S) (side : Bool) (p : Pairing) (top s : Bool) (y : ObjectSlot S)
      (ρ ρ' : List S.C), ObjectSlot.compat o side p top s f y = true → CEnv p top s ρ ρ' →
        AgreeHalf S side (fieldSem α β f ρ).codec (denote α β y.term ρ')
  | .req x, side, p, top, s, y, ρ, ρ', h, he => compat_sound ho x side p top s y.term ρ ρ' h he
  | .optional x, side, p, top, s, y, ρ, ρ', h, he =>
      compat_sound ho x side p top s y.term ρ ρ' h he
termination_by structural f => f
end

/-- **The decision at two closed options gives agreement on both halves.** -/
theorem compatPair_sound [PrimAdm S] [PrimAdmA S] [Leaf S] [LeafAdm S] [LeafMeet S] [FormerAdm S]
    [LeafAdmA S] [FormerAdmA S] [Shapes S] [TopLaws S] {o : CompatOracle S} (ho : OracleSound o) {x y : Term S}
    (h : compatPair o x y = true) :
    Agree .host (denote α β x) (denote α β y) ∧ Agree .dual (denote α β x) (denote α β y) := by
  simp only [compatPair, Bool.and_eq_true] at h
  have he : CEnv pair0 true true ([] : List S.C) [] :=
    ⟨fun _ _ _ hp => (nomatch hp), fun _ _ => sub_empty, fun _ _ => sub_empty, fun _ => ⟨rfl, rfl⟩⟩
  have hall := agree_all (compat_sound (α := α) (β := β) ho x true pair0 true true y [] [] h.1 he)
    (compat_sound (α := α) (β := β) ho x false pair0 true true y [] [] h.2 he)
  exact ⟨hall .host, hall .dual⟩


/-- **The decision discharges the union's obligation** of two lawful closed options: both halves
    agree, and over two lawful codecs the two halves are `Compat` in each order. -/
theorem pairwiseCompat_of_compatPair [PrimAdm S] [PrimAdmA S] [Leaf S] [LeafAdm S] [LeafMeet S] [FormerAdm S]
    [LeafAdmA S] [FormerAdmA S] [Shapes S] [TopLaws S] {o : CompatOracle S} (ho : OracleSound o) {x y : Term S}
    (h : compatPair o x y = true) (hl : ∀ t ∈ [x, y], Lawful Mean.mem (denote α β t)) :
    PairwiseCompat α β [x, y] := by
  obtain ⟨hE, hP⟩ := compatPair_sound (α := α) (β := β) ho h
  have hx := hl x (by simp)
  have hy := hl y (by simp)
  have hxy : Compat (denote α β x) (denote α β y) := (compat_iff_agree hx hy).mpr ⟨hE, hP⟩
  have hyx : Compat (denote α β y) (denote α β x) := compat_symm hx hy hxy
  intro s hs t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs ht
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · exact fun _ _ hp _ => hp
  · exact hxy
  · exact hyx
  · exact fun _ _ hp _ => hp

end Sound

end Calculus.Alg
