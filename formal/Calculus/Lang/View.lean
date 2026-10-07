import Calculus.Lang.DisjointA

/-!
# The views of a term, over a universe signature

A term denotes a partial isomorphism. The view at an orientation is a term with no `held` that
admits at the orientation each value that the term admits (`viewLe_of`). The view at the caller
side of a universe states the domain of the term, and the view at the dual states the range.
`Term.disjoint` reads no table, so the test reads a raw `held` as disjoint from the bottom alone.
The view replaces each `held` by a term that bounds its domain or its range, so two views that the
test separates give two terms that admit no common value (`views_apart`).

The proof reads the laws of the top (`TopLaws`). A view holds no `held`, so the view of a term
over an environment of restrictions of the top is a restriction of the top. A set of the view
then acts element by element, and the set law of the top carries the inclusion through the set.
-/

namespace Calculus

/-- The entry test of an object over wider slot rows and a wider open block admits where the
    narrower test admits. -/
theorem objAdmV_mono {α : Type} {fs : Finset String} {P Q : {k // k ∈ fs} → α → Bool}
    {wP wQ : Option (α → Bool)} (hf : ∀ k, RowLe (P k) (Q k)) (hw : Option.Rel RowLe wP wQ)
    {keys : Finset String} {g : {k // k ∈ keys} → α}
    (h : objAdmV ⟨fs, P⟩ wP keys g = true) : objAdmV ⟨fs, Q⟩ wQ keys g = true := by
  unfold objAdmV at h ⊢
  refine decide_eq_true fun k => ?_
  have := of_decide_eq_true h k
  rcases Decidable.em (k.1 ∈ fs) with hm | hm
  · simp only [entryP, MapOf.at, dif_pos hm] at this ⊢
    exact hf ⟨k.1, hm⟩ _ this
  · simp only [entryP, MapOf.at, dif_neg hm] at this ⊢
    cases hw with
    | none => exact this
    | some hr => exact hr _ this

end Calculus

namespace Calculus.Alg

/-! ## The view -/

section View
variable {B : Sig} [Mean B]

mutual
/-- **The view at an orientation**: each `held` becomes its term at the caller side of the
    orientation: its outer where its side is that caller side, and its inner term otherwise. The
    view of a `union` is the union of the views, because a union admits where one of its options
    admits. The view at the host is the caller view, and the view at the dual is the stored view.

    The view of `mu b` is `mu` of the view of `b`, and a variable stays a variable. Each stage of
    the view admits what the same stage of the term admits, so the view of a recursive term
    admits what the term admits. The view holds no `held` (`HF_view`), so a set of the view acts
    element by element.

    **Over a held-free closed inner term, the view keeps a refinement as it is.** Elsewhere the
    inner term can hold a `held`: a free variable can name a codec that holds one, so a free
    variable counts as a possible `held`. A bound variable denotes a stage of a binder inside the
    term, and `hasHeld` reads the binder's body, so a bound variable holds no `held` there. The
    orientation tests the predicate of its caller side directly, and tests the predicate of its
    stored side through the map of the inner term, which runs the adapter. The view keeps no
    adapter, so the view keeps the predicate of the caller side and puts the truth of the meaning
    at the stored side.

    **The stored view is narrower than it can be.** A free variable holds a `held` only where the
    codec that it names holds one, so a finer view keeps more predicates over a free variable.
    `Term.disjoint` compares a data predicate only over a closed held-free inner term, so a
    predicate over a free variable changes no verdict of the test. -/
def view (o : Orient) : Term B → Term B
  | .held s t P _ _ => bif s == o.c then view o P else view o t
  | .refine t p pA =>
      if hasHeld t || !t.closed then
        .refine (view o t) (bif o.c then Mean.truth false else p)
          (bif o.c then pA else Mean.truth true)
      else .refine t p pA
  | .list pre sp suf => .list (viewL o pre) (viewO o sp) (viewL o suf)
  | .object b => .object (viewB o b)
  | .union os => .union (viewL o os)
  | .set t => .set (view o t)
  | .mu b => .mu (view o b)
  -- the write is the inner term's; the older reader is opaque, so the read is bounded by `opaque`
  | .legacy t _ => bif o.c then .opaq else view o t
  | t => t
/-- The view of each term of a list. -/
def viewL (o : Orient) : List (Term B) → List (Term B)
  | [] => []
  | t :: ts => view o t :: viewL o ts
/-- The view of an optional term. -/
def viewO (o : Orient) : Option (Term B) → Option (Term B)
  | none => none
  | some t => some (view o t)
/-- The view of a body: the view of each slot and of the open block. -/
def viewB (o : Orient) : Body B → Body B
  | .mk fs f w => .mk fs (fun k => viewS o (f k)) (viewO o w)
/-- The view of a slot. -/
def viewS (o : Orient) : ObjectSlot B → ObjectSlot B
  | .req t => .req (view o t)
  | .optional t => .optional (view o t)
  -- the caller side always holds the name; the stored side may lack it
  | .fill t _ => bif o.c then .optional (view o t) else .req (view o t)
end

mutual
/-- **The view holds no `held`.** Each `held` becomes its view, and a refinement that the view
    keeps as it is has an inner term with no `held`. -/
theorem HF_view (o : Orient) : ∀ t : Term B, hasHeld (view o t) = false
  | .held s t P _ _ => by
      simp only [view]; cases s == o.c
      exacts [HF_view o t, HF_view o P]
  | .legacy t _ => by
      simp only [view]; cases o.c
      exacts [HF_view o t, rfl]
  | .refine t _ _ => by
      simp only [view]
      split
      · exact HF_view o t
      · next h =>
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h
        exact h.1
  | .list pre sp suf => by
      simp only [view, hasHeld, Bool.or_eq_false_iff]
      exact ⟨⟨HF_viewL o pre, HF_viewO o sp⟩, HF_viewL o suf⟩
  | .object (.mk fs f w) => by
      simp only [view, viewB, hasHeld, hasHeldB, Bool.or_eq_false_iff, decide_eq_false_iff_not,
        not_exists]
      exact ⟨fun k => Bool.eq_false_iff.mp (HF_viewS o (f k)), HF_viewO o w⟩
  | .union os => by simp only [view]; exact HF_viewL o os
  | .set t => by simp only [view]; exact HF_view o t
  | .mu b => by simp only [view]; exact HF_view o b
  | .prim _ => rfl | .opaq => rfl | .never => rfl | .var _ => rfl
/-- `HF_view` over a list. -/
theorem HF_viewL (o : Orient) : ∀ ts : List (Term B), hasHeldL (viewL o ts) = false
  | [] => rfl
  | t :: ts => by
      simp only [viewL, hasHeldL, Bool.or_eq_false_iff]; exact ⟨HF_view o t, HF_viewL o ts⟩
/-- `HF_view` at an optional term. -/
theorem HF_viewO (o : Orient) : ∀ x : Option (Term B), hasHeldO (viewO o x) = false
  | none => rfl
  | some t => HF_view o t
/-- `HF_view` at a slot. -/
theorem HF_viewS (o : Orient) : ∀ s : ObjectSlot B, hasHeldS (viewS o s) = false
  | .req t => HF_view o t
  | .optional t => HF_view o t
  | .fill t _ => by
      rcases Bool.eq_false_or_eq_true o.c with hc | hc <;>
        simp only [viewS, hc, cond_true, cond_false] <;> exact HF_view o t
end

/-- **The caller predicate of the view of a refinement is the caller predicate of the
    refinement.** -/
theorem half_view_c (p : B.P false) (pA : B.P true) : ∀ c : Bool,
    half c (bif c then Mean.truth false else p) (bif c then pA else Mean.truth true) = half c p pA
  | false => rfl
  | true => rfl

/-- **The stored predicate of the view of a refinement is the truth.** -/
theorem half_view_s (p : B.P false) (pA : B.P true) : ∀ c s : Bool, c ≠ s →
    half s (bif c then Mean.truth false else p) (bif c then pA else Mean.truth true) =
      Mean.truth s
  | false, true, _ => rfl
  | true, false, _ => rfl
  | false, false, h => absurd rfl h
  | true, true, h => absurd rfl h

end View

/-! ## The view admits what the term admits -/

/-- **An older reader changes no write**: at an orientation whose caller side is `false`, the
    codec with an older reader moves what the codec moves. -/
theorem extendRead_f_of_c {V M : Type} (c : Codec V M) (r : V → Option V) :
    ∀ o : Orient, o.c = false → (c.extendRead r).f o = c.f o :=
  Orient.both (P := fun o => o.c = false → (c.extendRead r).f o = c.f o)
    (fun _ => rfl) (fun h => nomatch h)

section Le
variable {S : Syn} [Sem S]

/-- The second environment acts, at each index and at the orientation of the universe, where the
    first acts. -/
def EnvLe (ρ ρ' : List S.C) : Prop :=
  ∀ i x, ((envAt ρ i).f S.o x).isSome = true → ((envAt ρ' i).f S.o x).isSome = true

/-- Each codec of the environment is a restriction of the top. -/
def EnvSub (ρ : List S.C) : Prop := ∀ i, Sub (envAt ρ i) (Syn.top (S := S))

/-- A codec that acts more, on top of an environment that acts more. -/
theorem EnvLe.cons {c c' : S.C} {ρ ρ' : List S.C}
    (hc : ∀ x, (c.f S.o x).isSome = true → (c'.f S.o x).isSome = true) (h : EnvLe ρ ρ') :
    EnvLe (c :: ρ) (c' :: ρ')
  | 0 => hc
  | i + 1 => h i

/-- A restriction of the top, on top of an environment of restrictions of the top. -/
theorem EnvSub.cons {c : S.C} {ρ : List S.C} (hc : Sub c (Syn.top (S := S))) (h : EnvSub ρ) :
    EnvSub (c :: ρ)
  | 0 => hc
  | i + 1 => h i

/-- The empty environment gives the bottom at each index. -/
theorem EnvSub.nil : EnvSub (S := S) [] := fun _ => sub_empty

/-- **The top at each index acts where any environment acts.** -/
theorem EnvLe.top : ∀ ρ : List S.C, EnvLe ρ (ρ.map fun _ => Syn.top (S := S))
  | [] => fun _ _ h => absurd h Bool.false_ne_true
  | _ :: ρ => EnvLe.cons (fun _ _ => rfl) (EnvLe.top ρ)

/-- The top at each index is a restriction of the top. -/
theorem EnvSub.top : ∀ ρ : List S.C, EnvSub (ρ.map fun _ => Syn.top (S := S))
  | [] => EnvSub.nil
  | _ :: ρ => EnvSub.cons (fun _ _ _ h => h) (EnvSub.top ρ)

variable [PrimAdm S] (α : Table S) (β : Table S.op)

mutual
/-- **The view admits at the orientation each value that the term admits**, under an
    environment that acts at each index where the first environment acts. One proof serves both
    orientations: the value side at the universe, and the attribute side at the dual.

    The environment is what the `mu` row needs. A recursive term admits what its body admits over
    the stage below the depth of the value (`Adm_mu_unfold`), and the view does the same over the
    stage of the view. An induction over the stages carries the inclusion to each stage. The
    environment of the view is a restriction of the top, because the view holds no `held`, and the
    `set` row reads a restriction of the top through the set law of the top.

    A `held` and a refinement over a possible `held` are the two rows that read the orientation.
    A refinement that the view keeps as it is has a closed inner term, so the environment does
    not change its map (`denote_of_closed`). -/
theorem viewLeE [TopLaws S] : ∀ (t : Term S) (ρ ρ' : List S.C), EnvLe ρ ρ' → EnvSub ρ' →
    RowLe (Adm α β t ρ) (Adm α β (view S.o t) ρ')
  | .held s t P k₀ k, ρ, ρ', he, hs => fun v h => by
      simp only [Adm, Bool.and_eq_true] at h
      simp only [view]
      cases hc : (s == S.o.c)
      · have hne : S.o.c ≠ s := fun h' => by rw [h'] at hc; cases s <;> exact absurd hc (by decide)
        have h1 := h.1.1
        rw [PairAt.one_ne s _ S.o.c hne] at h1
        exact viewLeE t ρ ρ' he hs v h1
      · have h2 := h.1.2
        have hP : Adm α β P ρ v = true := by
          revert h2 hc; generalize S.o.c = c
          cases s <;> cases c <;> intro hc h2 <;> first | exact absurd hc (by decide) | exact h2
        exact viewLeE P ρ ρ' he hs v hP
  | .var i, _, _, he, _ => fun v h => by
      rw [Adm_eq_isSome] at h ⊢
      exact he i v h
  | .mu b, ρ, ρ', he, hs => fun v h => by
      simp only [view]
      rw [Adm_mu_unfold] at h ⊢
      have hst : ∀ n, (∀ w, ((muStage (fun c => denote α β b (c :: ρ)) n).f S.o w).isSome = true →
          ((muStage (fun c => denote α β (view S.o b) (c :: ρ')) n).f S.o w).isSome = true) ∧
          Sub (muStage (fun c => denote α β (view S.o b) (c :: ρ')) n) (Syn.top (S := S)) := by
        intro n
        induction n with
        | zero => exact ⟨(fun _ hw => nomatch hw), sub_empty⟩
        | succ n ih =>
          have he' := EnvLe.cons ih.1 he
          have hs' := EnvSub.cons ih.2 hs
          refine ⟨fun w hw => ?_, sub_denoteIn (α := α) (β := β) (view S.o b) (HF_view S.o b) _ hs'⟩
          have := viewLeE b _ _ he' hs' w (by rw [Adm_eq_isSome]; exact hw)
          rwa [Adm_eq_isSome] at this
      exact viewLeE b _ _ (EnvLe.cons (hst _).1 he) (EnvSub.cons (hst _).2 hs) v h
  | .legacy t r, ρ, ρ', he, hs => fun v h => by
      simp only [view]
      rcases Bool.eq_false_or_eq_true S.o.c with hc | hc
      · rw [hc]; rfl
      · rw [hc]
        refine viewLeE t ρ ρ' he hs v ?_
        rw [Adm_eq_isSome] at h ⊢
        rw [show denote α β (.legacy t r) ρ = (denote α β t ρ).extendRead (Mean.read r) from rfl,
          extendRead_f_of_c _ _ S.o hc] at h
        exact h
  | .refine t p pA, ρ, ρ', he, hs => fun v h => by
      simp only [view]
      split
      · simp only [Adm, Bool.and_eq_true] at h ⊢
        have hw := viewLeE t ρ ρ' he hs v h.1.1
        refine ⟨⟨hw, ?_⟩, ?_⟩
        · rw [half_view_c p pA S.o.c]; exact h.1.2
        · rw [half_view_s p pA S.o.c S.o.s S.o.2]
          rw [Adm_eq_isSome] at hw
          show gate ((denote α β (view S.o t) ρ').f S.o) (Mean.eval S.o.s (Mean.truth S.o.s)) v = true
          rw [show Mean.eval (B := S.sig) S.o.s (Mean.truth S.o.s) = fun _ => true from
            funext (Mean.eval_truth S.o.s)]
          exact (gate_true _ _).trans hw
      · next hv =>
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hv
        rw [Adm_eq_isSome] at h ⊢
        rwa [denote_of_closed (α := α) (β := β) (.refine t p pA)
          (by simpa [Term.closed, Term.readsFree] using hv.2) ρ' ρ]
  | .list pre sp suf, ρ, ρ', he, hs => fun v h => by
      cases hl : listOut (S := S) v with
      | none => rw [Adm_list_of_none hl] at h; exact absurd h Bool.false_ne_true
      | some vs =>
        rw [Adm_list_of_out hl] at h
        simp only [view]; rw [Adm_list_of_out hl]
        exact alignPL_mono (viewLeEL pre ρ ρ' he hs) (viewLeEO sp ρ ρ' he hs)
          (viewLeEL suf ρ ρ' he hs) vs h
  | .object (.mk fs f w), ρ, ρ', he, hs => fun v h => by
      rw [Adm_object] at h
      change AdmBody α β (.mk fs (fun k => viewS S.o (f k)) (viewO S.o w)) ρ' v = true
      cases hm : mapOut (S := S) v with
      | none => rw [AdmBody_of_none hm] at h; exact absurd h Bool.false_ne_true
      | some m =>
        rw [AdmBody_of_out hm] at h; rw [AdmBody_of_out hm]
        simp only [Body.fields_mk, Body.at_mk, Body.wild_mk] at h ⊢
        rw [Bool.and_eq_true] at h ⊢
        refine ⟨?_, objAdmV_mono (fun k => viewLeES (f k) ρ ρ' he hs) ?_ h.2⟩
        · refine decide_eq_true fun k hr => of_decide_eq_true h.1 k ?_
          beta_reduce at hr
          generalize f k = s at hr
          rcases Bool.eq_false_or_eq_true S.o.c with hc | hc <;>
            cases s <;> simp_all [viewS, ObjectSlot.isReqAt]
        · cases w with
          | none => exact .none
          | some t => exact .some (viewLeE t ρ ρ' he hs)
  | .union os, ρ, ρ', he, hs => fun v h => anyP_mono (viewLeEL os ρ ρ' he hs) v h
  | .set t, ρ, ρ', he, hs => fun v h => by
      simp only [view]
      rw [Adm_eq_isSome] at h ⊢
      simp only [denote, denoteAbs] at h ⊢
      cases hL : Mean.set (B := S.sig) with
      | none => rw [hL] at h; exact h
      | some L =>
        rw [hL] at h
        exact TopLaws.set_mono L hL S.o _ _
          (sub_denoteIn (α := α) (β := β) _ (HF_view S.o t) ρ' hs)
          (fun w hw => by
            have := viewLeE t ρ ρ' he hs w (by rw [Adm_eq_isSome]; exact hw)
            rwa [Adm_eq_isSome] at this) v h
  | .prim _, _, _, _, _ => fun _ h => h
  | .opaq, _, _, _, _ => fun _ h => h
  | .never, _, _, _, _ => fun _ h => h
/-- `viewLeE` over a list. -/
theorem viewLeEL [TopLaws S] : ∀ (ts : List (Term S)) (ρ ρ' : List S.C), EnvLe ρ ρ' → EnvSub ρ' →
    List.Forall₂ RowLe (AdmList α β ts ρ) (AdmList α β (viewL S.o ts) ρ')
  | [], _, _, _, _ => .nil
  | t :: ts, ρ, ρ', he, hs => .cons (viewLeE t ρ ρ' he hs) (viewLeEL ts ρ ρ' he hs)
/-- `viewLeE` at an optional term. -/
theorem viewLeEO [TopLaws S] : ∀ (x : Option (Term S)) (ρ ρ' : List S.C), EnvLe ρ ρ' → EnvSub ρ' →
    Option.Rel RowLe (AdmOptT α β x ρ) (AdmOptT α β (viewO S.o x) ρ')
  | none, _, _, _, _ => .none
  | some t, ρ, ρ', he, hs => .some (viewLeE t ρ ρ' he hs)
/-- `viewLeE` at a slot. -/
theorem viewLeES [TopLaws S] : ∀ (s : ObjectSlot S) (ρ ρ' : List S.C), EnvLe ρ ρ' → EnvSub ρ' →
    RowLe (AdmField α β s ρ) (AdmField α β (viewS S.o s) ρ')
  | .req t, ρ, ρ', he, hs => viewLeE t ρ ρ' he hs
  | .optional t, ρ, ρ', he, hs => viewLeE t ρ ρ' he hs
  | .fill t _, ρ, ρ', he, hs => by
      rcases Bool.eq_false_or_eq_true S.o.c with hc | hc <;>
        simp only [viewS, hc, cond_true, cond_false] <;> exact viewLeE t ρ ρ' he hs
end

/-- **The view admits at the orientation each value that the term admits**, under any
    environment: the view reads the top at each index. -/
theorem viewLe_of [TopLaws S] (t : Term S) (ρ : List S.C) :
    RowLe (Adm α β t ρ) (Adm α β (view S.o t) (ρ.map fun _ => Syn.top (S := S))) :=
  viewLeE α β t ρ _ (EnvLe.top ρ) (EnvSub.top ρ)

/-- **Two terms whose views at the orientation are disjoint admit no common value there**, under
    any two environments. A value that both terms admit is admitted by both views (`viewLe_of`),
    and the views share no value (`disjoint_sound`). One proof serves both halves of a
    certificate: the value side at the universe, and the attribute side at the dual. -/
theorem views_apart [TopLaws S] [Leaf S] [LeafAdm S] [LeafMeet S] [FormerAdm S] [Shapes S] {x y : Term S}
    (h : Term.disjoint pair0 (view S.o x) (view S.o y) = true) (ρ ρ' : List S.C) (v : S.V) :
    (Adm α β x ρ v && Adm α β y ρ' v) = false :=
  apart_of_imp (viewLe_of α β x ρ v) (apart_of_imp' (viewLe_of α β y ρ' v)
    (disjoint_sound (α := α) (β := β) pair0 _ _ h _ _ (fun _ _ hp => nomatch hp) v))

end Le

end Calculus.Alg
