import Calculus.Lang.Term

/-!
# The judgement over a universe signature

`⊢ c : T ⇝ μ` is `Typed t T μ`. `T` is the held set, a predicate on the caller carrier, and `μ` is
the member that the stored side stamps. Each rule builds its held set from the held sets of its
premises, with the former of the container: the list and map formers read the prisms of the
universe, and the set former and the top read the held sets that the universe names.

A container rule takes its former as a premise, `Sem.list = some L`. A universe without the former
types no term of the container, and its denotation of such a term is the bottom.

`Obligations` holds the semantic premises of the rules: the cancellation of each half of a
`held`, the pairwise compatibility of a union, the universe's own set obligation, and the premises
of a binder's body at each stage.
-/

namespace Calculus.Alg

/-! ## Held sets -/

section Held
variable {V : Type}

/-- The positional part of `T₁ × … × Tₙ`, and of `… × T*` when a tail is present:
    the fixed head matched position by position, the tail uniformly. -/
def HTuple : List (V → Prop) → Option (V → Prop) → List V → Prop
  | [], none, vs => vs = []
  | [], some T, vs => ∀ x ∈ vs, T x
  | _ :: _, _, [] => False
  | T :: Ts, tl, v :: vs => T v ∧ HTuple Ts tl vs

/-- The positional part of a `list`'s held set: the suffix splits off the right end, and
    what is left is `HTuple`'s prefix-and-spread. `Forall₂` carries both the length of the
    suffix and the holding at each of its positions, so no length premise is owed. -/
def HTupleL (pre : List (V → Prop)) (sp : Option (V → Prop)) (suf : List (V → Prop)) (vs : List V) :
    Prop :=
  ∃ front back : List V,
    vs = front ++ back ∧ List.Forall₂ (fun T v => T v) suf back ∧ HTuple pre sp front

/-- `T₁ × … × Tₚ × T* × U₁ × … × U_s` (§3 `(list)`): the one positional held set, through the
    list prism of the universe. -/
def HList (pV : Ctor (List V) V) (pre : List (V → Prop)) (sp : Option (V → Prop))
    (suf : List (V → Prop)) : V → Prop :=
  fun v => ∃ vs, v = pV.into vs ∧ HTupleL pre sp suf vs

/-- `⟨n₁ :^π₁ T₁ … nₙ :^πₙ Tₙ⟩ ⊕ R(ρ)` (§4 `(object)`), through the map prism of the universe. A
    binding is `(required?, held set)`, and `R` is the held set of the open block. Every `req` name
    is present, and every present name is either declared, and holds its own set, or falls to the
    open block. -/
def HObject (mV : Ctor (MapOf V) V) (names : Finset String)
    (b : {k // k ∈ names} → Bool × (V → Prop)) (R : Option (V → Prop)) : V → Prop :=
  fun v => ∃ keys f, v = mV.into ⟨keys, f⟩ ∧
    (∀ k : {k // k ∈ names}, (b k).1 = true → k.1 ∈ keys) ∧
    (∀ k : {k // k ∈ keys},
      if h : k.1 ∈ names then (b ⟨k.1, h⟩).2 (f k)
      else ∃ T, R = some T ∧ T (f k))

/-- `⋃ Tᵢ` (§5 `(union)`). -/
def HUnion (Ts : List (V → Prop)) : V → Prop :=
  fun v => ∃ T ∈ Ts, T v

/-- The bottom's held set: nothing. It is disjoint from every held set. -/
def HNever : V → Prop := fun _ => False

end Held

/-! ## The judgement -/

variable {S : Syn} [Sem S] [SynA S] [SemA S] {α : Table S} {β : Table S.op}

variable (α β) in
mutual

inductive Typed : Term S → (S.V → Prop) → Option (Sem.M S) → Prop where
  /-- §3's ground rules, as one rule: the held set is the primitive codec's, and the member is the
      one the universe names. -/
  | prim (g : S.Ground) : Typed (.prim g) (Sem.ground g).T (Sem.groundμ g)
  /-- §3 `(set)`: the element's judgement, lifted by the set former of the universe. -/
  | set {L t T μ} (hL : Sem.set (S := S) = some L) (h : Typed t T μ) :
      Typed (.set t) (L.held T) (μ.bind L.member)
  /-- `(list)`: one rule for the one positional container. -/
  | list {L pre Tpre sp Tsp suf Tsuf} (hL : Sem.list (S := S) = some L)
      (hp : TypedList pre Tpre) (hs : TypedOpt sp Tsp) (hf : TypedList suf Tsuf) :
      Typed (.list pre sp suf) (HList L.pV Tpre Tsp Tsuf) (some L.μ)
  /-- `(held)`: the held set **is** the premise's, pulled back along `f`, and cut by the
      admission of the caller-side term `P`; the cancellation laws are `Obligations`'.

      No premise relating `T` to `I`, because `adapt2` *defines* `T := fun v => c.T (f v)`.
      `P` carries no judgement, as the predicate of `refine` carries none: the rule reads only the
      domain of its codec. The stored outer `PA` and the stored word act on the stored side only,
      so they leave the held set alone. -/
  | held {t I μ P PA k kA} (h : Typed t I μ) :
      Typed (.held t P PA k kA) (fun v => I ((α.word k).1 v) ∧ ((denote α β P).e v).isSome) μ
  | refine {t T μ p pA} (h : Typed t T μ) :
      Typed (.refine t p pA) (fun v => T v ∧ Sem.eval p v) μ
  | opaq : Typed .opaq Sem.topHeld none
  /-- §5's bottom. It writes no value, so it stores no member, and its held set is `False`. -/
  | never : Typed .never HNever none
  /-- §4 `(object)`. The field table is a key set with a function on it, so the judgement is
      **pointwise**: every declared name's field is typed at its binding, and the bindings are
      indexed by the same set. -/
  | object {F} {body : Body S} {bind R} {μs : {k // k ∈ body.fields} → Option (Sem.M S)}
      (hF : Sem.map (S := S) = some F)
      (hf : ∀ k, TypedField (body.at k) (bind k).2 (bind k).1 (μs k))
      (hr : TypedWild body.wild R) :
      Typed (.object body) (HObject F.mV body.fields bind R) (some F.μ)
  /-- `(union)`: the option judgements. -/
  | union {opts Ts μs} (h : TypedListμ opts Ts μs) :
      Typed (.union opts) (HUnion Ts) (unanimous μs)
  /-- A variable, read closed. No binder of the derivation gives it a codec, so it holds nothing.
      Under a `mu`, `soundness` reads the variable from the environment, and this index plays no
      part there. -/
  | var (i : Nat) : Typed (.var i) HNever none
  /-- `mu`: a guarded recursive term. The held set is the limit's own, which is its write domain
      (`muCodec`). The body's judgement is the premise that `soundness` reads at each stage. `hg`
      is the guard, a checked condition on the syntax (`Term.guarded`), and it refuses an
      unguarded binder at construction. -/
  | mu {b T μ} (hg : (Term.mu b).guarded = true) (h : Typed b T μ) :
      Typed (.mu b) (fun v => (denote α β (.mu b)).T v) none

inductive TypedList : List (Term S) → List (S.V → Prop) → Prop where
  | nil : TypedList [] []
  | cons {t ts T Ts μ} (h : Typed t T μ) (hs : TypedList ts Ts) :
      TypedList (t :: ts) (T :: Ts)

/-- The option judgements of a `(union)`, held sets and members kept: the rule's
    conclusion is computed from them (`HUnion`, `unanimous`), as in the doc. -/
inductive TypedListμ : List (Term S) → List (S.V → Prop) → List (Option (Sem.M S)) → Prop where
  | nil : TypedListμ [] [] []
  | cons {t ts T Ts μ μs} (h : Typed t T μ) (hs : TypedListμ ts Ts μs) :
      TypedListμ (t :: ts) (T :: Ts) (μ :: μs)

inductive TypedOpt : Option (Term S) → Option (S.V → Prop) → Prop where
  | none : TypedOpt none none
  | some {t T μ} (h : Typed t T μ) : TypedOpt (some t) (some T)

/-- §4's `⊢ f : T ⊗ π ⇝ μ`; the `Bool` is `π`, `true` for `req`. -/
inductive TypedField : ObjectSlot S → (S.V → Prop) → Bool → Option (Sem.M S) → Prop where
  | req {t T μ} (h : Typed t T μ) : TypedField (.req t) T true μ
  | optional {t T μ} (h : Typed t T μ) : TypedField (.optional t) T false μ

/-- §4's `⊢ ρ : wild`, carrying `R(ρ)`: `none` where the body carries no open block, the open
    block's held set otherwise. -/
inductive TypedWild : Option (Term S) → Option (S.V → Prop) → Prop where
  | none : TypedWild none none
  | some {t T μ} (h : Typed t T μ) : TypedWild (some t) (some T)

end

/-! ## Reading a field's judgement

`TypedField`'s indices at a declared name are `(b k).2`, `(b k).1` and `μs k` — none of
them a variable — so `cases` on it cannot eliminate. These two extract what the callers
want without eliminating at the use site. -/

/-- A typed field gives its term, that term's judgement, and its shape. -/
theorem TypedField.term {fd : ObjectSlot S} {T π μ} (h : TypedField α β fd T π μ) :
    ∃ t', Typed α β t' T μ ∧
      (fd = .req t' ∨ fd = .optional t') := by
  cases h with
  | req h' => exact ⟨_, h', Or.inl rfl⟩
  | optional h' => exact ⟨_, h', Or.inr rfl⟩

/-- …and a required one is not optional. -/
theorem TypedField.not_optional {fd : ObjectSlot S} {T π μ} (h : TypedField α β fd T π μ)
    (hπ : π = true) : ∀ t', fd ≠ .optional t' := by
  cases h with
  | req _ => intro t' hc; exact nomatch hc
  | optional _ => exact absurd hπ (by simp)

/-- …and the same fact read the other way: a field that is not `optional` is required.

    `not_optional` is what a *consumer* of the judgement wants — it has `π = true` and needs
    the shape. Producing `π = true` from the shape is the converse, and `typed_T_eq`'s
    `object` case is where it is needed: there the map's key set is known to contain every
    required name and the guard `valPresentB` is stated by shape, so the two have to be
    exchanged in this direction. Both rows are `rfl`. -/
theorem TypedField.true_of_not_optional {fd : ObjectSlot S} {T π μ} (h : TypedField α β fd T π μ)
    (hno : ∀ t', fd ≠ .optional t') : π = true := by
  cases h with
  | req _ => rfl
  | optional _ => exact absurd rfl (hno _)


/-! ## Reading the list judgements -/

/-- Each element of a typed list is typed. -/
theorem TypedList.forall : ∀ {ts : List (Term S)} {Ts}, TypedList α β ts Ts → ∀ t ∈ ts, ∃ T μ, Typed α β t T μ
  | _, _, .nil, t, ht => absurd ht (by simp)
  | _, _, .cons h hs, t, ht => by
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact ⟨_, _, h⟩
      · exact TypedList.forall hs t ht'

/-- Each option of a typed union is typed. -/
theorem TypedListμ.forall : ∀ {ts : List (Term S)} {Ts μs}, TypedListμ α β ts Ts μs →
    ∀ t ∈ ts, ∃ T μ, Typed α β t T μ
  | _, _, _, .nil, t, ht => absurd ht (by simp)
  | _, _, _, .cons h hs, t, ht => by
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact ⟨_, _, h⟩
      · exact TypedListμ.forall hs t ht'

/-- A union option's held set is one of the rule's. -/
theorem TypedListμ.mem : ∀ {ts : List (Term S)} {Ts μs}, TypedListμ α β ts Ts μs →
    ∀ t ∈ ts, ∃ T ∈ Ts, ∃ μ, Typed α β t T μ
  | _, _, _, .nil, t, ht => absurd ht (by simp)
  | _, _, _, .cons h hs, t, ht => by
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact ⟨_, List.mem_cons_self, _, h⟩
      · obtain ⟨T', hT', μ', hty⟩ := TypedListμ.mem hs t ht'
        exact ⟨T', List.mem_cons_of_mem _ hT', μ', hty⟩

/-! ## The member index -/

mutual

/-- The member a term stores, syntactically: the `⇝` index computed from the term. -/
def μSyn : Term S → Option (Sem.M S)
  | .prim g => Sem.groundμ g
  | .set t =>
      match Sem.set (S := S) with
      | some L => (μSyn t).bind L.member
      | none => none
  | .list _ _ _ => (Sem.list (S := S)).map (·.μ)
  | .held t _ _ _ _ => μSyn t
  | .refine t _ _ => μSyn t
  | .opaq | .var _ | .mu _ | .never => none
  | .object _ => (Sem.map (S := S)).map (·.μ)
  | .union opts => unanimous (μSynList opts)

def μSynList : List (Term S) → List (Option (Sem.M S))
  | [] => []
  | t :: ts => μSyn t :: μSynList ts

end

mutual

/-- Typing's member index is the syntactic one. -/
theorem typed_μSyn : ∀ {t : Term S} {T μ}, Typed α β t T μ → μSyn t = μ
  | _, _, _, .prim _ => rfl
  | _, _, _, .set hL h' => by simp only [μSyn, hL, typed_μSyn h']
  | _, _, _, .list hL _ _ _ => by simp only [μSyn, hL, Option.map_some]
  | _, _, _, .held h' => by rw [μSyn]; exact typed_μSyn h'
  | _, _, _, .refine h' => by rw [μSyn]; exact typed_μSyn h'
  | _, _, _, .opaq | _, _, _, .never | _, _, _, .var _ | _, _, _, .mu _ _ => rfl
  | _, _, _, .object hF _ _ => by simp only [μSyn, hF, Option.map_some]
  | _, _, _, .union h => congrArg unanimous (typedListμ_μSyn h)

/-- …and the options' members, per option. -/
theorem typedListμ_μSyn : ∀ {ts : List (Term S)} {Ts μs}, TypedListμ α β ts Ts μs → μSynList ts = μs
  | _, _, _, .nil => rfl
  | _, _, _, .cons h hs => by rw [μSynList, typed_μSyn h, typedListμ_μSyn hs]

end

/-! ## Obligations -/

variable (α β) in
/-- **The union's obligation**: its options are pairwise compatible. -/
def PairwiseCompat (opts : List (Term S)) (ρ : List S.C := []) : Prop :=
  ∀ s ∈ opts, ∀ t ∈ opts, Compat (denote α β s ρ) (denote α β t ρ)

/-- The universe's own set obligation on an element, where the universe has a set former. -/
def SetObl (c : S.C) : Prop :=
  match Sem.set (S := S) with
  | some L => L.elem c
  | none => True

variable (α β) in
mutual

/-- The doc's semantic rule premises.

    **Structural**, and it means what the specification means: the premises hold. The list
    companions exist because `∀ t' ∈ ts, Obligations t'` is not a structural recursion and
    `ObligationsList` is. -/
def Obligations : Term S → (ρ : List S.C := []) → Prop
  | .prim _, _ | .opaq, _ | .never, _ | .var _, _ => True
  -- the element's premises, and the universe's set obligation
  | .set t', ρ => Obligations t' ρ ∧ SetObl (denote α β t' ρ)
  | .refine t' _ _, ρ => Obligations t' ρ
  | .list pre sp suf, ρ => ObligationsList pre ρ ∧ ObligationsOpt sp ρ ∧ ObligationsList suf ρ
  -- the two outers owe nothing: a restriction keeps the laws of any lawful codec
  | .held t' _ _ k kA, ρ => Obligations t' ρ ∧
      Obl2 Sem.member (denote α β t' ρ) (α.word k).1 (α.word k).2 (β.word kA).1 (β.word kA).2
  | .object b, ρ => ObligationsBody b ρ
  | .union opts, ρ => ObligationsList opts ρ ∧ PairwiseCompat α β opts ρ
  -- the body's premises at each stage, given that the stage before is lawful
  | .mu b, ρ => ∀ n, Lawful Sem.member (muStage (fun c => denote α β b (c :: ρ)) n) →
      Obligations b (muStage (fun c => denote α β b (c :: ρ)) n :: ρ)

/-- The payload's premises: every declared slot's, and the open block's. -/
def ObligationsBody : Body S → (ρ : List S.C := []) → Prop
  | .mk _ f wild, ρ => (∀ k, ObligationsField (f k) ρ) ∧ ObligationsWild wild ρ

/-- A slot's premises are the current-schema term's premises. -/
def ObligationsField : ObjectSlot S → (ρ : List S.C := []) → Prop
  | .req t', ρ => Obligations t' ρ
  | .optional t', ρ => Obligations t' ρ

def ObligationsWild : Option (Term S) → (ρ : List S.C := []) → Prop
  | some t', ρ => Obligations t' ρ
  | none, _ => True

def ObligationsList : List (Term S) → (ρ : List S.C := []) → Prop
  | [], _ => True
  | t' :: ts, ρ => Obligations t' ρ ∧ ObligationsList ts ρ

def ObligationsOpt : Option (Term S) → (ρ : List S.C := []) → Prop
  | none, _ => True
  | some t', ρ => Obligations t' ρ

end

/-! ### The companions, as the quantifiers a proof speaks in -/

/-- A list's premises are each element's. -/
theorem obligationsList_iff {ρ : List S.C} : ∀ {ts : List (Term S)},
    ObligationsList α β ts ρ ↔ ∀ t ∈ ts, Obligations α β t ρ
  | [] => by simp [ObligationsList]
  | t :: ts => by
      simp only [ObligationsList, List.mem_cons, forall_eq_or_imp]
      exact and_congr_right (fun _ => obligationsList_iff)

/-- An optional term's premises are the term's, where the term is present. -/
theorem obligationsOpt_iff {ρ : List S.C} : ∀ {tail : Option (Term S)},
    ObligationsOpt α β tail ρ ↔ ∀ t ∈ tail, Obligations α β t ρ
  | none => by simp [ObligationsOpt]
  | some _ => by simp [ObligationsOpt]

end Calculus.Alg
