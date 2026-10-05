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
closed-context oracle of the universe decides orthogonality of each half. A `held` acts inside
its outer on the half at its side, and inside its inner term on the other half. So a `held` whose
half is disjoint from the partner agrees there. Two `held`s of one side and one word agree where
their inner terms agree. A
container agrees with a container of its former where the components agree.

The contexts: one per operand, they say which variables are below the top, so the held-free row
applies to two held-free terms whose free variables are below the top. The oracle reads two closed
terms, which denote alike in every environment. `compat_sound` states agreement of the denotations
over every two environments that the pairing and the contexts admit. At the empty contexts the
decision holds at every environment, so `pairwiseCompat_of_compatPair` discharges the union's
obligation of two lawful options, whatever codec a free variable later names.
-/

namespace Calculus.Alg

variable {S : Syn}

/-- The oracles that a universe supplies: an orthogonality test for each half at the closed
    context. -/
structure CompatOracle (S : Syn) where
  orthE : Term S → Term S → Bool
  orthP : Term S → Term S → Bool

/-- **Where one half of a term acts.** A half reads the caller side of its orientation: the write
    half reads the caller side of the universe, and the read half reads the stored side. The half
    at the side of a `held` sits inside its outer, and the other half sits inside its inner term,
    because the other side has no adapter. Where that term is a `held` too, the half sits inside
    its side in turn. Any other term is its own side. -/
def heldSideIn (side : Bool) : Term S → Term S
  | .held sd i P _ _ =>
      match (bif side then S.o else S.o.op).c == sd with
      | true => heldSideIn side P
      | false => heldSideIn side i
  | t => t

/-- The row a `held` gives one half: the term inside which the half acts. -/
def heldSide (side : Bool) : Term S → Option (Term S)
  | .held sd i P k₀ k => some (heldSideIn side (.held sd i P k₀ k))
  | _ => none

/-- **The empty context**: no variable is known to be below the top. -/
def noSafe : Nat → Bool := fun _ => false

/-- **The entry that a binder `mu b` pushes onto the context of its side**: the binder is below the
    top where `b` is held-free and each free variable of `mu b` is safe. -/
def pushMu (ctx : Nat → Bool) (b : Term S) : Nat → Bool :=
  ctxPush (!hasHeld b && (Term.mu b).safe ctx) ctx

/-- **The rows that read no structure**: the bottom, two held-free terms whose free variables are
    below the top, two disjoint terms, the closed-context oracle at two closed terms, and a `held`
    whose half is disjoint from the partner. -/
def cbase [Leaf S] (o : CompatOracle S) (side : Bool) (cl cr : Nat → Bool) (x y : Term S) : Bool :=
  x.isNever || y.isNever || (!hasHeld x && !hasHeld y && x.safe cl && y.safe cr) ||
    Term.disjoint pair0 x y || (x.closed && y.closed && (if side then o.orthE x y else o.orthP x y)) ||
    (match heldSide side x with | some h => Term.disjoint pair0 h y | none => false) ||
    (match heldSide side y with | some h => Term.disjoint pair0 x h | none => false)

mutual
/-- **The rows of the right operand.** The bottom, a union option by option, a refinement
    through its inner term, and a recursive term unfolded with its binder paired with nothing. -/
def cmpR (fam : Pairing → (Nat → Bool) → (Nat → Bool) → Term S → Bool) (p : Pairing) (cl cr : Nat → Bool) :
    Term S → Bool
  | .never => true
  | .union os => fam p cl cr (.union os) || cmpRL fam p cl cr os
  | .refine y q qA => fam p cl cr (.refine y q qA) || cmpR fam p cl cr y
  | .mu b => fam p cl cr (.mu b) || cmpR fam (shiftR p) cl (pushMu cr b) b
  | y => fam p cl cr y
def cmpRL (fam : Pairing → (Nat → Bool) → (Nat → Bool) → Term S → Bool) (p : Pairing) (cl cr : Nat → Bool) :
    List (Term S) → Bool
  | [] => true
  | y :: ys => cmpR fam p cl cr y && cmpRL fam p cl cr ys
end

/-- The term of a slot, whatever its presence. -/
def ObjectSlot.term : ObjectSlot S → Term S
  | .req t | .optional t | .fill t _ => t

/-- Every test of the left row against every term of the right row. -/
def allPairs (fs : List (Term S → Bool)) (ys : List (Term S)) : Bool :=
  fs.all fun f => ys.all f

/-- **Two slots answer alike at absence** on a half, the host's stand-in test: on the read, a
    fill agrees with a `req` slot, which reads no map without the name, and with no other slot.
    Two fills are refused: the constants have no decidable equality. -/
def ObjectSlot.absentAgree (o : Orient) (a b : ObjectSlot S) : Bool :=
  !o.c || match a, b with
    | .fill _ _, .req _ | .req _, .fill _ _ => true
    | .fill _ _, _ | _, .fill _ _ => false
    | _, _ => true

mutual
/-- **The compatibility decision, one half.** Structural on the left operand. -/
def Term.compat [Leaf S] (o : CompatOracle S) (side : Bool) (p : Pairing) (cl cr : Nat → Bool) :
    Term S → Term S → Bool
  | .never, _ => true
  | .refine x q qA, y => cbase o side cl cr (.refine x q qA) y || Term.compat o side p cl cr x y
  | .union os, y => cbase o side cl cr (.union os) y || Term.compatL o side p cl cr os y
  | .mu b, .mu b' => cbase o side cl cr (.mu b) (.mu b') ||
      (Term.compat o true (pairMu p) (pushMu cl b) (pushMu cr b') b b' &&
        Term.compat o false (pairMu p) (pushMu cl b) (pushMu cr b') b b')
  | .mu b, y => cbase o side cl cr (.mu b) y ||
      Term.compat o side (shiftL p) (pushMu cl b) cr b y
  | .var i, y => cmpR (fun p' cl' cr' y' => cbase o side cl' cr' (.var i) y' ||
      (match y' with | .var j => p' i j | _ => false)) p cl cr y
  | .held sd i P k₀ k, y => cmpR (fun p' cl' cr' y' => cbase o side cl' cr' (.held sd i P k₀ k) y' ||
      (match y' with
        | .held sd' i' _ k₀' k' =>
            decide ((⟨sd, k₀ :: k⟩ : (sd : Bool) × List (S.sig.G sd × Bool)) = ⟨sd', k₀' :: k'⟩) &&
              Term.compat o side p' cl' cr' i i'
        | _ => false)) p cl cr y
  | .prim g, y => cmpR (fun _ cl' cr' y' => cbase o side cl' cr' (.prim g) y') p cl cr y
  | .opaq, y => cmpR (fun _ cl' cr' y' => cbase o side cl' cr' .opaq y') p cl cr y
  -- the older reader is opaque, so a legacy term is decided by the base test alone
  | .legacy x r, y => cmpR (fun _ cl' cr' y' => cbase o side cl' cr' (.legacy x r) y') p cl cr y
  | .set a, y => cmpR (fun p' cl' cr' y' => cbase o side cl' cr' (.set a) y' ||
      (match y' with | .set a' => Term.compat o side p' cl' cr' a a' | _ => false)) p cl cr y
  | .list pre sp suf, y => cmpR (fun p' cl' cr' y' => cbase o side cl' cr' (.list pre sp suf) y' ||
      (match y' with
        | .list pre' sp' suf' =>
            allPairs (Term.compatTs o side p' cl' cr' pre ++ Term.compatO o side p' cl' cr' sp ++
              Term.compatTs o side p' cl' cr' suf) (pre' ++ sp'.toList ++ suf')
        | _ => false)) p cl cr y
  | .object (.mk fs f w), y => cmpR (fun p' cl' cr' y' => cbase o side cl' cr' (.object (.mk fs f w)) y' ||
      (match y' with
        | .object b' =>
            decide (∀ k : {k // k ∈ fs ∪ b'.fields},
              (if h : k.1 ∈ fs then ObjectSlot.compat o side p' cl' cr' (f ⟨k.1, h⟩) (b'.slotAt k.1)
               else Term.compatW o side p' cl' cr' w (b'.slotAt k.1).term) = true) &&
            decide (∀ k : {k // k ∈ fs ∪ b'.fields}, ObjectSlot.absentAgree
              (bif side then S.o else S.o.op) ((Body.mk fs f w).slotAt k.1) (b'.slotAt k.1) = true) &&
            Term.compatW o side p' cl' cr' w b'.block
        | _ => false)) p cl cr y
termination_by structural x _ => x
/-- A union is compatible with the right operand where each option is. -/
def Term.compatL [Leaf S] (o : CompatOracle S) (side : Bool) (p : Pairing) (cl cr : Nat → Bool) :
    List (Term S) → Term S → Bool
  | [], _ => true
  | x :: xs, y => Term.compat o side p cl cr x y && Term.compatL o side p cl cr xs y
termination_by structural xs _ => xs
/-- The test at each position of a row, partially applied. -/
def Term.compatTs [Leaf S] (o : CompatOracle S) (side : Bool) (p : Pairing) (cl cr : Nat → Bool) :
    List (Term S) → List (Term S → Bool)
  | [] => []
  | t :: ts => Term.compat o side p cl cr t :: Term.compatTs o side p cl cr ts
termination_by structural ts => ts
/-- …at the spread. -/
def Term.compatO [Leaf S] (o : CompatOracle S) (side : Bool) (p : Pairing) (cl cr : Nat → Bool) :
    Option (Term S) → List (Term S → Bool)
  | none => []
  | some t => [Term.compat o side p cl cr t]
termination_by structural t => t
/-- …at the open block: a closed body holds the bottom there. -/
def Term.compatW [Leaf S] (o : CompatOracle S) (side : Bool) (p : Pairing) (cl cr : Nat → Bool) :
    Option (Term S) → Term S → Bool
  | none, _ => true
  | some t, y => Term.compat o side p cl cr t y
termination_by structural t => t
/-- Two slots at one name: the terms, whatever the presence. A fill also needs `absentAgree`. -/
def ObjectSlot.compat [Leaf S] (o : CompatOracle S) (side : Bool) (p : Pairing) (cl cr : Nat → Bool) :
    ObjectSlot S → ObjectSlot S → Bool
  | .req x, y | .optional x, y | .fill x _, y => Term.compat o side p cl cr x y.term
termination_by structural f _ => f
end

/-- **The decision at two options**: both halves, at the empty contexts, where each free variable is
    unknown. It holds at every environment (`compatPair_sound`). -/
def compatPair [Leaf S] (o : CompatOracle S) (x y : Term S) : Bool :=
  Term.compat o true pair0 noSafe noSafe x y && Term.compat o false pair0 noSafe noSafe x y


/-- **Agreement on one half of a universe**: the write half (`side = true`) is agreement at the
    orientation of the universe, and the read half is agreement at the dual orientation. -/
abbrev AgreeHalf (S : Syn) {V M : Type} (side : Bool) (c d : Codec V M) : Prop :=
  Agree (bif side then S.o else S.o.op) c d

section Sound
variable [Sem S] {α : Table S} {β : Table S.op}

/-- **What the contexts and the pairing promise of the two environments.** A paired binder pair
    agrees on both halves. Each entry that a context marks safe is below the top. -/
structure CEnv (p : Pairing) (cl cr : Nat → Bool) (ρ ρ' : List S.C) : Prop where
  pair : ∀ i j, p i j = true → ∀ o, Agree o (envAt ρ i) (envAt ρ' j)
  safeL : ∀ i, cl i = true → Sub (envAt ρ i) (Syn.top (S := S))
  safeR : ∀ i, cr i = true → Sub (envAt ρ' i) (Syn.top (S := S))

/-- What the oracles promise, at every table. -/
structure OracleSound (o : CompatOracle S) : Prop where
  e : ∀ {α : Table S} {β : Table S.op} x y, o.orthE x y = true → ∀ v,
    (((denote α β x []).f S.o v).isSome && ((denote α β y []).f S.o v).isSome) = false
  p : ∀ {α : Table S} {β : Table S.op} x y, o.orthP x y = true → ∀ a,
    (((denote α β x []).f S.o.op a).isSome && ((denote α β y []).f S.o.op a).isSome) = false

/-- **The empty contexts promise nothing of the environments**, so they admit every two. -/
theorem CEnv.empty (ρ ρ' : List S.C) : CEnv pair0 noSafe noSafe ρ ρ' where
  pair _ _ h := nomatch h
  safeL _ h := nomatch h
  safeR _ h := nomatch h

/-- **A stage is below the top where its binder pushes a safe entry.** -/
theorem stage_subMu [TopLaws S] {b : Term S} {ctx : Nat → Bool} {ρ : List S.C}
    (h : (!hasHeld b && (Term.mu b).safe ctx) = true)
    (henv : ∀ i, ctx i = true → Sub (envAt ρ i) (Syn.top (S := S))) (n : Nat) :
    Sub (muStage (fun c => denote α β b (c :: ρ)) n) (Syn.top (S := S)) := by
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  exact stage_subSafe h.1 h.2 henv n

/-- An unfolding of the left operand keeps the promise: the new left binder pairs with nothing. -/
theorem CEnv.left {p : Pairing} {cl cr : Nat → Bool} {ρ ρ' : List S.C} (he : CEnv p cl cr ρ ρ')
    (b : Term S) (c : S.C) (hc : (!hasHeld b && (Term.mu b).safe cl) = true → Sub c (Syn.top (S := S))) :
    CEnv (shiftL p) (pushMu cl b) cr (c :: ρ) ρ' where
  pair i j h o := match i, h with
    | i + 1, h => he.pair i j h o
  safeL i h := match i with
    | 0 => hc h
    | i + 1 => he.safeL i h
  safeR := he.safeR

/-- …and an unfolding of the right operand. -/
theorem CEnv.right {p : Pairing} {cl cr : Nat → Bool} {ρ ρ' : List S.C} (he : CEnv p cl cr ρ ρ')
    (b : Term S) (c : S.C) (hc : (!hasHeld b && (Term.mu b).safe cr) = true → Sub c (Syn.top (S := S))) :
    CEnv (shiftR p) cl (pushMu cr b) ρ (c :: ρ') where
  pair i j h o := match j, h with
    | j + 1, h => he.pair i j h o
  safeL := he.safeL
  safeR i h := match i with
    | 0 => hc h
    | i + 1 => he.safeR i h

/-- Two binders unfolded together keep the promise where their stages agree on both halves. -/
theorem CEnv.mu {p : Pairing} {cl cr : Nat → Bool} {ρ ρ' : List S.C} (he : CEnv p cl cr ρ ρ')
    (b b' : Term S) (c c' : S.C) (hcc : ∀ o, Agree o c c')
    (hc : (!hasHeld b && (Term.mu b).safe cl) = true → Sub c (Syn.top (S := S)))
    (hc' : (!hasHeld b' && (Term.mu b').safe cr) = true → Sub c' (Syn.top (S := S))) :
    CEnv (pairMu p) (pushMu cl b) (pushMu cr b') (c :: ρ) (c' :: ρ') where
  pair i j h o := match i, j, h with
    | 0, 0, _ => hcc o
    | i + 1, j + 1, h => he.pair i j h o
  safeL i h := match i with
    | 0 => hc h
    | i + 1 => he.safeL i h
  safeR i h := match i with
    | 0 => hc' h
    | i + 1 => he.safeR i h

/-- A disjoint pair has apart write domains, over every two environments. -/
theorem disjoint_domE [PrimAdm S] [Leaf S] [LeafAdm S] [LeafMeet S] [FormerAdm S] [Shapes S]
    [TopLaws S] {x y : Term S} (h : Term.disjoint pair0 x y = true) (ρ ρ' : List S.C) (v : S.V) :
    (((denote α β x ρ).f S.o v).isSome && ((denote α β y ρ').f S.o v).isSome) = false := by
  have := disjoint_sound (α := α) (β := β) pair0 x y h ρ ρ' (fun _ _ hp => nomatch hp) v
  rwa [Adm_eq_isSome, Adm_eq_isSome] at this

/-- …and apart read domains. -/
theorem disjoint_domP [PrimAdmA S] [Leaf S] [LeafMeet S] [LeafAdmA S] [FormerAdmA S] [Shapes S]
    [TopLaws S] {x y : Term S} (h : Term.disjoint pair0 x y = true) (ρ ρ' : List S.C) (a : S.V) :
    (((denote α β x ρ).f S.o.op a).isSome && ((denote α β y ρ').f S.o.op a).isSome) = false := by
  have := disjoint_soundA (α := α) (β := β) pair0 x y h ρ ρ' (fun _ _ hp => nomatch hp) a
  rwa [AdmA_eq_isSome, AdmA_eq_isSome] at this

/-- **A `held` acts at an orientation only where its outer acts**, where its side is the caller
    side of the orientation, and only where its inner term acts otherwise. -/
theorem held_dom {sd : Bool} {i P : Term S} {k₀ : S.sig.G sd × Bool} {k : List (S.sig.G sd × Bool)}
    {ρ : List S.C} (o : Orient) (x : Mean.V (B := S.sig))
    (h : ((denote α β (.held sd i P k₀ k) ρ).f o x).isSome = true) :
    ((denote α β (if o.c == sd then P else i) ρ).f o x).isSome = true := by
  have h' : ((held1 sd (denote α β i ρ) (denote α β P ρ)
      ((tables S.o α β sd).word (k₀ :: k))).f o x).isSome = true := h
  rw [held1_f_isSome, Bool.and_eq_true] at h'
  -- by the four cases: the lemmas of a lawful BEq reach the choice axiom through an order instance
  have hne : ∀ a b : Bool, (a == b) = false → a ≠ b
    | false, false, h, _ | true, true, h, _ => nomatch h
  have heq : ∀ a b : Bool, (a == b) = true → a = b
    | false, false, _ | true, true, _ => rfl
    | false, true, h | true, false, h => nomatch h
  cases hs : (o.c == sd)
  · rw [PairAt.one_ne _ _ _ (hne _ _ hs)] at h'
    rw [if_neg Bool.false_ne_true]
    exact gate_isSome h'.2
  · obtain rfl := heq _ _ hs
    rw [if_pos rfl]
    rw [bne, hs, Bool.not_true, Bool.false_or] at h'
    exact h'.1

/-- **A half acts only inside the term where it sits**: the domain of a term at the orientation of
    a half lies inside the domain of `heldSideIn`, by `held_dom` at each `held` on the way. -/
theorem heldSideIn_dom (side : Bool) {ρ : List S.C} :
    ∀ (t : Term S) (x : Mean.V (B := S.sig)),
      ((denote α β t ρ).f (bif side then S.o else S.o.op) x).isSome = true →
        ((denote α β (heldSideIn side t) ρ).f (bif side then S.o else S.o.op) x).isSome = true
  | .held sd i P k₀ k, x, h => by
      have h' := held_dom (k₀ := k₀) (k := k) (bif side then S.o else S.o.op) x h
      simp only [heldSideIn]
      cases hc : ((bif side then S.o else S.o.op).c == sd)
      · rw [hc] at h'
        exact heldSideIn_dom side i x h'
      · rw [hc] at h'
        exact heldSideIn_dom side P x h'
  | .prim _, _, h | .opaq, _, h | .never, _, h | .var _, _, h | .mu _, _, h | .set _, _, h
  | .refine _ _ _, _, h | .legacy _ _, _, h | .list _ _ _, _, h | .union _, _, h | .object _, _, h => by
      simpa only [heldSideIn] using h

/-- **The rows that read no structure are sound.** -/
theorem cbase_sound [PrimAdm S] [PrimAdmA S] [Leaf S] [LeafAdm S] [LeafMeet S] [FormerAdm S]
    [LeafAdmA S] [FormerAdmA S] [Shapes S] [TopLaws S] {o : CompatOracle S} (ho : OracleSound o) {side : Bool}
    {cl cr : Nat → Bool} {x y : Term S} (h : cbase o side cl cr x y = true) {p : Pairing}
    {ρ ρ' : List S.C} (he : CEnv p cl cr ρ ρ') : AgreeHalf S side (denote α β x ρ) (denote α β y ρ') := by
  simp only [cbase, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with ((((((hx | hy) | ⟨⟨⟨hx, hy⟩, hsx⟩, hsy⟩) | hd) | ⟨⟨hcx, hcy⟩, ho'⟩) | hl) | hr)
  · cases x <;> simp only [Term.isNever, reduceCtorEq] at hx
    exact agree_empty_left _ _
  · cases y <;> simp only [Term.isNever, reduceCtorEq] at hy
    exact agree_empty_right _ _
  · exact agree_bound (sub_denoteSafe x cl hx hsx ρ he.safeL) (sub_denoteSafe y cr hy hsy ρ' he.safeR)
  · cases side
    · exact agree_apart (disjoint_domP hd ρ ρ')
    · exact agree_apart (disjoint_domE hd ρ ρ')
  · -- two closed terms denote alike in every environment, so the oracle at `[]` speaks for them
    rw [denote_of_closed x hcx ρ [], denote_of_closed y hcy ρ' []]
    cases side
    · exact agree_apart (ho.p x y ho')
    · exact agree_apart (ho.e x y ho')
  · cases x <;> simp only [heldSide, reduceCtorEq] at hl
    cases side
    · exact agree_apart fun a =>
        apart_of_imp (heldSideIn_dom false _ a) (disjoint_domP hl ρ ρ' a)
    · exact agree_apart fun v =>
        apart_of_imp (heldSideIn_dom true _ v) (disjoint_domE hl ρ ρ' v)
  · cases y <;> simp only [heldSide, reduceCtorEq] at hr
    cases side
    · exact agree_apart fun a =>
        apart_of_imp' (heldSideIn_dom false _ a) (disjoint_domP hr ρ ρ' a)
    · exact agree_apart fun v =>
        apart_of_imp' (heldSideIn_dom true _ v) (disjoint_domE hr ρ ρ' v)

mutual
/-- **The rows of the right operand are sound**, for a left codec that the family is sound for. -/
theorem cmpR_sound [TopLaws S] {side : Bool} {X : S.C} {ρ : List S.C}
    {fam : Pairing → (Nat → Bool) → (Nat → Bool) → Term S → Bool}
    (hfam : ∀ p' cl' cr' y' ρ', fam p' cl' cr' y' = true → CEnv p' cl' cr' ρ ρ' →
      AgreeHalf S side X (denote α β y' ρ')) :
    ∀ (y : Term S) (p : Pairing) (cl cr : Nat → Bool) (ρ' : List S.C), cmpR fam p cl cr y = true →
      CEnv p cl cr ρ ρ' → AgreeHalf S side X (denote α β y ρ')
  | .never, _, _, _, _, _, _ => agree_empty_right _ X
  | .union os, p, cl, cr, ρ', h, he => by
      simp only [cmpR, Bool.or_eq_true] at h
      rcases h with h | h
      · exact hfam _ _ _ _ _ h he
      · simp only [denote, denoteAbs]
        exact agree_alt_right (cmpRL_sound hfam os p cl cr ρ' h he)
  | .refine y q _, p, cl, cr, ρ', h, he => by
      simp only [cmpR, Bool.or_eq_true] at h
      rcases h with h | h
      · exact hfam _ _ _ _ _ h he
      · simp only [denote, denoteAbs]
        exact agree_sub_right (sub_refine2_self _ _ _) (cmpR_sound hfam y p cl cr ρ' h he)
  | .mu b, p, cl, cr, ρ', h, he => by
      simp only [cmpR, Bool.or_eq_true] at h
      rcases h with h | h
      · exact hfam _ _ _ _ _ h he
      · simp only [denote, denoteAbs]
        refine agree_mu_right fun n => ?_
        cases n with
        | zero => exact agree_empty_right _ X
        | succ n =>
          exact cmpR_sound hfam b (shiftR p) cl (pushMu cr b) (_ :: ρ') h
            (he.right b _ fun hs => stage_subMu hs he.safeR n)
  | .prim _, _, _, _, _, h, he => hfam _ _ _ _ _ h he
  | .set _, _, _, _, _, h, he => hfam _ _ _ _ _ h he
  | .list _ _ _, _, _, _, _, h, he => hfam _ _ _ _ _ h he
  | .held _ _ _ _ _, _, _, _, _, h, he => hfam _ _ _ _ _ h he
  | .opaq, _, _, _, _, h, he => hfam _ _ _ _ _ h he
  | .legacy _ _, _, _, _, _, h, he => hfam _ _ _ _ _ h he
  | .object _, _, _, _, _, h, he => hfam _ _ _ _ _ h he
  | .var _, _, _, _, _, h, he => hfam _ _ _ _ _ h he
/-- …and option by option. -/
theorem cmpRL_sound [TopLaws S] {side : Bool} {X : S.C} {ρ : List S.C}
    {fam : Pairing → (Nat → Bool) → (Nat → Bool) → Term S → Bool}
    (hfam : ∀ p' cl' cr' y' ρ', fam p' cl' cr' y' = true → CEnv p' cl' cr' ρ ρ' →
      AgreeHalf S side X (denote α β y' ρ')) :
    ∀ (ys : List (Term S)) (p : Pairing) (cl cr : Nat → Bool) (ρ' : List S.C),
      cmpRL fam p cl cr ys = true → CEnv p cl cr ρ ρ' → ∀ o ∈ denoteList α β ys ρ', AgreeHalf S side X o
  | [], _, _, _, _, _, _ => fun _ h => nomatch h
  | y :: ys, p, cl, cr, ρ', h, he => by
      simp only [cmpRL, Bool.and_eq_true] at h
      intro o ho
      simp only [denoteList_cons, List.mem_cons] at ho
      rcases ho with rfl | ho
      · exact cmpR_sound hfam y p cl cr ρ' h.1 he
      · exact cmpRL_sound hfam ys p cl cr ρ' h.2 he o ho
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

/-- An undeclared name acts at absence as the open block's `optional` slot. -/
theorem absentOf_slotAt (fs : Finset String) (f : {k // k ∈ fs} → ObjectSlot S)
    (w : Option (Term S)) (o : Orient) (ρ : List S.C) (k : String) :
    absentOf o ((⟨fs, fun k => fieldSem α β (f k) ρ⟩ : MapOf _).at k) =
      absentOf o (some (fieldSem α β ((Body.mk fs f w).slotAt k) ρ)) := by
  rcases Decidable.em (k ∈ fs) with hk | hk
  · rw [MapOf.at_of_mem (m := ⟨fs, _⟩) ⟨k, hk⟩, Body.slotAt_pos (b := .mk fs f w) hk]; rfl
  · rw [MapOf.at_none (m := ⟨fs, _⟩) hk, Body.slotAt_neg (b := .mk fs f w) hk]; rfl

/-- Two slots that `absentAgree` answer alike at absence. -/
theorem absentAgree_sound {o : Orient} {a b : ObjectSlot S} {ρ ρ' : List S.C} {y₁ y₂ : Option S.V}
    (h : ObjectSlot.absentAgree o a b = true)
    (e1 : absentOf o (some (fieldSem α β a ρ)) = some y₁)
    (e2 : absentOf o (some (fieldSem α β b ρ')) = some y₂) : y₁ = y₂ := by
  rcases Bool.eq_false_or_eq_true o.c with hc | hc <;> cases a <;> cases b <;>
    simp_all [ObjectSlot.absentAgree, absentOf, fieldSem, fieldSemAbs]

mutual
/-- **Soundness of the compatibility decision.** Where the decision answers `true` for one half,
    the two denotations agree on that half, over every two environments that the pairing and
    the flags admit. -/
theorem compat_sound [PrimAdm S] [PrimAdmA S] [Leaf S] [LeafAdm S] [LeafMeet S] [FormerAdm S]
    [LeafAdmA S] [FormerAdmA S] [Shapes S] [TopLaws S] {o : CompatOracle S} (ho : OracleSound o) :
    ∀ (x : Term S) (side : Bool) (p : Pairing) (cl cr : Nat → Bool) (y : Term S) (ρ ρ' : List S.C),
      Term.compat o side p cl cr x y = true → CEnv p cl cr ρ ρ' →
        AgreeHalf S side (denote α β x ρ) (denote α β y ρ')
  | .never, side, _, _, _, _, _, _, _, _ => agree_empty_left _ _
  | .refine x q _, side, p, cl, cr, y, ρ, ρ', h, he => by
      simp only [Term.compat, Bool.or_eq_true] at h
      rcases h with h | h
      · exact cbase_sound ho h he
      · simp only [denote, denoteAbs]
        exact agree_sub_left (sub_refine2_self _ _ _) (compat_sound ho x side p cl cr y ρ ρ' h he)
  | .union os, side, p, cl, cr, y, ρ, ρ', h, he => by
      simp only [Term.compat, Bool.or_eq_true] at h
      rcases h with h | h
      · exact cbase_sound ho h he
      · simp only [denote, denoteAbs]
        exact agree_alt_left (compatL_sound ho os side p cl cr y ρ ρ' h he)
  | .mu b, side, p, cl, cr, y, ρ, ρ', h, he => by
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
              have he' := he.mu b b' _ _ ih (fun hs => stage_subMu hs he.safeL n)
                (fun hs => stage_subMu hs he.safeR n)
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
            refine compat_sound ho b side (shiftL p) (pushMu cl b) cr _ _ ρ' h
              (he.left b _ fun hs => stage_subMu hs he.safeL n)
  | .var i, side, p, cl, cr, y, ρ, ρ', h, he => by
      simp only [Term.compat] at h
      refine cmpR_sound (fun p' cl' cr' y' ρ'' hf he' => ?_) y p cl cr ρ' h he
      simp only [Bool.or_eq_true] at hf
      rcases hf with hf | hf
      · exact cbase_sound ho hf he'
      · cases y' <;> simp only [reduceCtorEq] at hf
        rename_i j
        exact he'.pair i j hf _
  | .held sd i P k₀ k, side, p, cl, cr, y, ρ, ρ', h, he => by
      simp only [Term.compat] at h
      refine cmpR_sound (fun p' cl' cr' y' ρ'' hf he' => ?_) y p cl cr ρ' h he
      simp only [Bool.or_eq_true] at hf
      rcases hf with hf | hf
      · exact cbase_sound ho hf he'
      · cases y' <;> simp only [reduceCtorEq] at hf
        rename_i sd' i' P' k₀' k'
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
        obtain ⟨h1, h3⟩ := hf
        cases h1
        exact agree_of_agreeS (fun _ => agreeS_held1) _ (compat_sound ho i side p' cl' cr' i' ρ ρ'' h3 he')
  | .prim g, side, p, cl, cr, y, ρ, ρ', h, he => by
      simp only [Term.compat] at h
      exact cmpR_sound (fun p' cl' cr' y' ρ'' hf he' => cbase_sound ho hf he') y p cl cr ρ' h he
  | .opaq, side, p, cl, cr, y, ρ, ρ', h, he => by
      simp only [Term.compat] at h
      exact cmpR_sound (fun p' cl' cr' y' ρ'' hf he' => cbase_sound ho hf he') y p cl cr ρ' h he
  | .legacy x r, side, p, cl, cr, y, ρ, ρ', h, he => by
      simp only [Term.compat] at h
      exact cmpR_sound (fun p' cl' cr' y' ρ'' hf he' => cbase_sound ho hf he') y p cl cr ρ' h he
  | .set a, side, p, cl, cr, y, ρ, ρ', h, he => by
      simp only [Term.compat] at h
      refine cmpR_sound (fun p' cl' cr' y' ρ'' hf he' => ?_) y p cl cr ρ' h he
      simp only [Bool.or_eq_true] at hf
      rcases hf with hf | hf
      · exact cbase_sound ho hf he'
      · cases y' <;> simp only [reduceCtorEq] at hf
        rename_i a'
        have ih := compat_sound ho a side p' cl' cr' a' ρ ρ'' hf he'
        simp only [denote, denoteAbs]
        cases Mean.set (B := S.sig) with
        | none => exact agree_empty_left _ _
        | some L => exact agree_of_agreeS (fun _ => L.agreeS) _ ih
  | .list pre sp suf, side, p, cl, cr, y, ρ, ρ', h, he => by
      simp only [Term.compat] at h
      refine cmpR_sound (fun p' cl' cr' y' ρ'' hf he' => ?_) y p cl cr ρ' h he
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
        have hall : ∀ y ∈ pre' ++ sp'.toList ++ suf', ∀ f ∈ Term.compatTs o side p' cl' cr' pre ++
            Term.compatO o side p' cl' cr' sp ++ Term.compatTs o side p' cl' cr' suf, f y = true :=
          fun y hy f hf' => hf f hf' y hy
        have hpre := compatTs_sound ho pre side p' cl' cr' ρ ρ'' _
          (fun f hf' y hy => hall y hy f (by simp [hf'])) he'
        have hsp := compatO_sound ho sp side p' cl' cr' ρ ρ'' _
          (fun f hf' y hy => hall y hy f (by simp [hf'])) he'
        have hsuf := compatTs_sound ho suf side p' cl' cr' ρ ρ'' _
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
  | .object (.mk fs f w), side, p, cl, cr, y, ρ, ρ', h, he => by
      simp only [Term.compat] at h
      refine cmpR_sound (fun p' cl' cr' y' ρ'' hf he' => ?_) y p cl cr ρ' h he
      simp only [Bool.or_eq_true] at hf
      rcases hf with hf | hf
      · exact cbase_sound ho hf he'
      · cases y' <;> simp only [reduceCtorEq] at hf
        rename_i b'
        cases b' with
        | mk fs' f' w' =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
        obtain ⟨⟨hall, hfa⟩, hw⟩ := hf
        simp only [denote, denoteAbs, bodySemAbs]
        cases Mean.map (B := S.sig) with
        | none => exact agree_empty_left _ _
        | some F =>
          refine agree_object (fun k c₁ c₂ h1 h2 => ?_) (fun k y₁ y₂ e1 e2 => ?_)
          rotate_left
          · rw [absentOf_slotAt fs f w] at e1
            rw [absentOf_slotAt fs' f' w'] at e2
            rcases Decidable.em (k ∈ fs ∪ fs') with hk | hk
            · exact absentAgree_sound (hfa ⟨k, hk⟩) e1 e2
            · have h1 : k ∉ fs := fun h' => hk (Finset.mem_union.mpr (Or.inl h'))
              have h2 : k ∉ fs' := fun h' => hk (Finset.mem_union.mpr (Or.inr h'))
              rw [Body.slotAt_neg h1] at e1
              rw [Body.slotAt_neg h2] at e2
              cases e1; cases e2; rfl
          rcases entry_cases h1 with ⟨hk, rfl⟩ | ⟨hk, hc₁⟩ <;>
            rcases entry_cases h2 with ⟨hk', rfl⟩ | ⟨hk', hc₂⟩
          · have := hall ⟨k, Finset.mem_union.mpr (Or.inl hk)⟩
            simp only [dif_pos hk] at this
            have hs := cslot_sound ho (f ⟨k, hk⟩) side p' cl' cr' _ ρ ρ'' this he'
            rw [fieldSem_codec, Body.slotAt_pos hk'] at hs
            exact hs
          · have := hall ⟨k, Finset.mem_union.mpr (Or.inl hk)⟩
            simp only [dif_pos hk] at this
            have hs := cslot_sound ho (f ⟨k, hk⟩) side p' cl' cr' _ ρ ρ'' this he'
            rw [fieldSem_codec, Body.slotAt_neg hk'] at hs
            obtain ⟨u', rfl, rfl⟩ := rcOf_wild (α := α) (β := β) hc₂
            exact hs
          · have := hall ⟨k, Finset.mem_union.mpr (Or.inr hk')⟩
            simp only [dif_neg hk] at this
            have hs := compatW_sound ho w side p' cl' cr' _ ρ ρ'' this he' c₁ hc₁
            rw [Body.slotAt_pos hk'] at hs
            exact hs
          · obtain ⟨u', rfl, rfl⟩ := rcOf_wild (α := α) (β := β) hc₂
            exact compatW_sound ho w side p' cl' cr' _ ρ ρ'' hw he' c₁ hc₁
termination_by structural x => x
/-- …option by option. -/
theorem compatL_sound [PrimAdm S] [PrimAdmA S] [Leaf S] [LeafAdm S] [LeafMeet S] [FormerAdm S]
    [LeafAdmA S] [FormerAdmA S] [Shapes S] [TopLaws S] {o : CompatOracle S} (ho : OracleSound o) :
    ∀ (xs : List (Term S)) (side : Bool) (p : Pairing) (cl cr : Nat → Bool) (y : Term S)
      (ρ ρ' : List S.C), Term.compatL o side p cl cr xs y = true → CEnv p cl cr ρ ρ' →
        ∀ c ∈ denoteList α β xs ρ, AgreeHalf S side c (denote α β y ρ')
  | [], _, _, _, _, _, _, _, _, _ => fun _ h => nomatch h
  | x :: xs, side, p, cl, cr, y, ρ, ρ', h, he => by
      simp only [Term.compatL, Bool.and_eq_true] at h
      intro c hc
      simp only [denoteList_cons, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact compat_sound ho x side p cl cr y ρ ρ' h.1 he
      · exact compatL_sound ho xs side p cl cr y ρ ρ' h.2 he c hc
termination_by structural xs => xs
/-- …position by position. -/
theorem compatTs_sound [PrimAdm S] [PrimAdmA S] [Leaf S] [LeafAdm S] [LeafMeet S] [FormerAdm S]
    [LeafAdmA S] [FormerAdmA S] [Shapes S] [TopLaws S] {o : CompatOracle S} (ho : OracleSound o) :
    ∀ (ts : List (Term S)) (side : Bool) (p : Pairing) (cl cr : Nat → Bool) (ρ ρ' : List S.C)
      (ys : List (Term S)), (∀ f ∈ Term.compatTs o side p cl cr ts, ∀ y ∈ ys, f y = true) →
        CEnv p cl cr ρ ρ' → ∀ c ∈ denoteList α β ts ρ, ∀ y ∈ ys, AgreeHalf S side c (denote α β y ρ')
  | [], _, _, _, _, _, _, _, _, _ => fun _ h => nomatch h
  | t :: ts, side, p, cl, cr, ρ, ρ', ys, h, he => by
      intro c hc y hy
      simp only [denoteList_cons, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact compat_sound ho t side p cl cr y ρ ρ'
          (h _ (by simp [Term.compatTs]) y hy) he
      · exact compatTs_sound ho ts side p cl cr ρ ρ' ys
          (fun f hf y hy => h f (by simp [Term.compatTs, hf]) y hy) he c hc y hy
termination_by structural ts => ts
/-- …at the spread. -/
theorem compatO_sound [PrimAdm S] [PrimAdmA S] [Leaf S] [LeafAdm S] [LeafMeet S] [FormerAdm S]
    [LeafAdmA S] [FormerAdmA S] [Shapes S] [TopLaws S] {o : CompatOracle S} (ho : OracleSound o) :
    ∀ (t? : Option (Term S)) (side : Bool) (p : Pairing) (cl cr : Nat → Bool) (ρ ρ' : List S.C)
      (ys : List (Term S)), (∀ f ∈ Term.compatO o side p cl cr t?, ∀ y ∈ ys, f y = true) →
        CEnv p cl cr ρ ρ' → ∀ c, denoteOpt α β t? ρ = some c → ∀ y ∈ ys, AgreeHalf S side c (denote α β y ρ')
  | none, _, _, _, _, _, _, _, _, _ => fun _ h => nomatch h
  | some t, side, p, cl, cr, ρ, ρ', ys, h, he => by
      intro c hc y hy
      simp only [denoteOpt_some, Option.some.injEq] at hc
      subst hc
      exact compat_sound ho t side p cl cr y ρ ρ' (h _ (by simp [Term.compatO]) y hy) he
termination_by structural t? => t?
/-- …at the open block. -/
theorem compatW_sound [PrimAdm S] [PrimAdmA S] [Leaf S] [LeafAdm S] [LeafMeet S] [FormerAdm S]
    [LeafAdmA S] [FormerAdmA S] [Shapes S] [TopLaws S] {o : CompatOracle S} (ho : OracleSound o) :
    ∀ (w : Option (Term S)) (side : Bool) (p : Pairing) (cl cr : Nat → Bool) (y : Term S)
      (ρ ρ' : List S.C), Term.compatW o side p cl cr w y = true → CEnv p cl cr ρ ρ' →
        ∀ c, rcOf (wildSem α β w ρ) = some c → AgreeHalf S side c (denote α β y ρ')
  | none, _, _, _, _, _, _, _, _, _ => fun _ h => nomatch h
  | some t, side, p, cl, cr, y, ρ, ρ', h, he => by
      intro c hc
      simp only [wildSem, wildSemAbs, rcOf, Option.some.injEq] at hc
      subst hc
      exact compat_sound ho t side p cl cr y ρ ρ' h he
termination_by structural w => w
/-- …at one name. -/
theorem cslot_sound [PrimAdm S] [PrimAdmA S] [Leaf S] [LeafAdm S] [LeafMeet S] [FormerAdm S]
    [LeafAdmA S] [FormerAdmA S] [Shapes S] [TopLaws S] {o : CompatOracle S} (ho : OracleSound o) :
    ∀ (f : ObjectSlot S) (side : Bool) (p : Pairing) (cl cr : Nat → Bool) (y : ObjectSlot S)
      (ρ ρ' : List S.C), ObjectSlot.compat o side p cl cr f y = true → CEnv p cl cr ρ ρ' →
        AgreeHalf S side (fieldSem α β f ρ).codec (denote α β y.term ρ')
  | .req x, side, p, cl, cr, y, ρ, ρ', h, he => compat_sound ho x side p cl cr y.term ρ ρ' h he
  | .optional x, side, p, cl, cr, y, ρ, ρ', h, he =>
      compat_sound ho x side p cl cr y.term ρ ρ' h he
  | .fill x _, side, p, cl, cr, y, ρ, ρ', h, he =>
      compat_sound ho x side p cl cr y.term ρ ρ' h he
termination_by structural f => f
end

/-- **The decision gives agreement on both halves at every two environments**: the empty contexts
    promise nothing of the environments, so a free variable may name any codec. -/
theorem compatPair_sound [PrimAdm S] [PrimAdmA S] [Leaf S] [LeafAdm S] [LeafMeet S] [FormerAdm S]
    [LeafAdmA S] [FormerAdmA S] [Shapes S] [TopLaws S] {o : CompatOracle S} (ho : OracleSound o) {x y : Term S}
    (h : compatPair o x y = true) (ρ ρ' : List S.C) :
    Agree .host (denote α β x ρ) (denote α β y ρ') ∧ Agree .dual (denote α β x ρ) (denote α β y ρ') := by
  simp only [compatPair, Bool.and_eq_true] at h
  have hall := agree_all (compat_sound (α := α) (β := β) ho x true pair0 noSafe noSafe y ρ ρ' h.1
      (CEnv.empty ρ ρ'))
    (compat_sound (α := α) (β := β) ho x false pair0 noSafe noSafe y ρ ρ' h.2 (CEnv.empty ρ ρ'))
  exact ⟨hall .host, hall .dual⟩


/-- **The decision discharges the union's obligation** of two lawful options: both halves
    agree, and over two lawful codecs the two halves are `Compat` in each order. -/
theorem pairwiseCompat_of_compatPair [PrimAdm S] [PrimAdmA S] [Leaf S] [LeafAdm S] [LeafMeet S] [FormerAdm S]
    [LeafAdmA S] [FormerAdmA S] [Shapes S] [TopLaws S] {o : CompatOracle S} (ho : OracleSound o) {x y : Term S}
    (h : compatPair o x y = true) (hl : ∀ t ∈ [x, y], Lawful Mean.mem (denote α β t)) :
    PairwiseCompat α β [x, y] := by
  obtain ⟨hE, hP⟩ := compatPair_sound (α := α) (β := β) ho h [] []
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
