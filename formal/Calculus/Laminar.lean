import Calculus.HeldSet
import Calculus.ExactV

/-!
# (B): the held set is the admission

A derivable term whose obligations hold holds exactly the values that it admits (`typed_T_adm`), so the judgement's
index is `dom(e)` and not an upper bound. A union writes wherever one of its options writes, so
the union row needs no side condition.
-/

namespace Calculus

/-! ## The held set is the admission -/


/-- A term whose every held set is its admission. The induction hypothesis of `typed_T_adm`. -/
def AdmIff (t : Term) : Prop := ∀ T μ, Typed t T μ → ∀ v, T v ↔ Adm t v = true

/-- The rows of a term list are as many as the terms. -/
theorem AdmList_length (ts : List Term) : (AdmList ts).length = ts.length := by
  induction ts with
  | nil => rfl
  | cons t ts ihx => simp only [AdmList, List.length_cons, ihx]

/-- A spread holds a list exactly where the spread's row admits each element. -/
theorem htuple_nil_some_iff {t : Term} {T : Held} {μ} (hty : Typed t T μ) (ih : AdmIff t) :
    ∀ vs, HTuple [] (some T) vs ↔ alignP [] (some (Adm t)) vs = true
  | [] => by simp [HTuple, alignP]
  | x :: xs => by
      have := htuple_nil_some_iff hty ih xs
      simp only [HTuple, alignP, Bool.and_eq_true, List.forall_mem_cons] at this ⊢
      rw [ih _ _ hty x, this]

/-- `HTuple` is `alignP` at terms whose held sets are their admissions. -/
theorem htuple_iff {tail : Option Term} {Tt} (hopt : TypedOpt tail Tt)
    (iht : ∀ t' ∈ tail, AdmIff t') :
    ∀ {ts Ts}, TypedList ts Ts → (∀ t' ∈ ts, AdmIff t') →
      ∀ vs, HTuple Ts Tt vs ↔ alignP (AdmList ts) (AdmOptT tail) vs = true
  | _, _, .nil, _, vs => by
      cases hopt with
      | none => cases vs <;> simp [HTuple, alignP, AdmList, AdmOptT]
      | some hty => exact htuple_nil_some_iff hty (iht _ rfl) vs
  | _, _, .cons _ _, _, [] => by simp [HTuple, alignP, AdmList]
  | _, _, .cons hty hs, ih, v :: vs => by
      simp only [HTuple, AdmList, alignP, Bool.and_eq_true]
      rw [ih _ List.mem_cons_self _ _ hty v,
        htuple_iff hopt iht hs (fun t' h => ih t' (List.mem_cons_of_mem _ h)) vs]

/-- The suffix's held set is `zipP` at terms whose held sets are their admissions. -/
theorem zip_iff : ∀ {ts Ts}, TypedList ts Ts → (∀ t' ∈ ts, AdmIff t') →
    ∀ back, List.Forall₂ (fun (T : Held) v => T v) Ts back ↔ zipP (AdmList ts) back = true
  | _, _, .nil, _, [] => by simp [AdmList, zipP]
  | _, _, .nil, _, _ :: _ => by simp [AdmList, zipP]
  | _, _, .cons _ _, _, [] => by simp [AdmList, zipP]
  | _, _, .cons hty hs, ih, v :: vs => by
      simp only [List.forall₂_cons, AdmList, zipP, Bool.and_eq_true]
      rw [ih _ List.mem_cons_self _ _ hty v,
        zip_iff hs (fun t' h => ih t' (List.mem_cons_of_mem _ h)) vs]

/-- `HTupleL` is `alignPL` at terms whose held sets are their admissions. -/
theorem htupleL_iff {pre Tpre sp Tsp suf Tsuf} (hp : TypedList pre Tpre)
    (hs : TypedOpt sp Tsp) (hf : TypedList suf Tsuf)
    (ihp : ∀ t' ∈ pre, AdmIff t') (ihs : ∀ t' ∈ sp, AdmIff t') (ihf : ∀ t' ∈ suf, AdmIff t')
    (vs : List Value) :
    HTupleL Tpre Tsp Tsuf vs ↔ alignPL (AdmList pre) (AdmOptT sp) (AdmList suf) vs = true := by
  have hlen : (AdmList suf).length = Tsuf.length := by
    rw [AdmList_length, TypedList.length_eq hf]
  constructor
  · rintro ⟨front, back, rfl, hback, hfront⟩
    have hb : back.length = Tsuf.length := hback.length_eq.symm
    have hn : (front ++ back).length - (AdmList suf).length = front.length := by
      rw [hlen, List.length_append, hb]; omega
    simp only [alignPL, hn, List.take_left', List.drop_left', Bool.and_eq_true]
    exact ⟨(htuple_iff hs ihs hp ihp front).mp hfront, (zip_iff hf ihf back).mp hback⟩
  · intro h
    simp only [alignPL, Bool.and_eq_true] at h
    exact ⟨_, _, (List.take_append_drop _ vs).symm, (zip_iff hf ihf _).mpr h.2,
      (htuple_iff hs ihs hp ihp _).mpr h.1⟩

/-- A typed slot's mark is the slot's, and its held set is its admission. -/
theorem typedField_adm {s : ObjectSlot} {T b μ} (h : TypedField s T b μ)
    (ihr : ∀ t', s = .req t' → AdmIff t') (iho : ∀ t', s = .optional t' → AdmIff t') :
    b = s.isReq ∧ ∀ v, T v ↔ AdmField s v = true := by
  cases h with
  | req hty => exact ⟨rfl, fun v => ihr _ rfl _ _ hty v⟩
  | optional hty => exact ⟨rfl, fun v => iho _ rfl _ _ hty v⟩

/-- `HObject` is `AdmBody` at slots and an open block whose held sets are their admissions. -/
theorem hobject_iff {fields : Finset Name} {ff : {k // k ∈ fields} → ObjectSlot}
    {wild : Option Term} {bind : {k // k ∈ fields} → Bool × Held} {R : Option Held}
    {μs : {k // k ∈ fields} → Option Member}
    (hfields : ∀ k, TypedField (ff k) (bind k).2 (bind k).1 (μs k))
    (ihr : ∀ k t', ff k = .req t' → AdmIff t') (iho : ∀ k t', ff k = .optional t' → AdmIff t')
    (hrest : TypedWild wild R) (ihw : ∀ t', wild = some t' → AdmIff t') (v : Value) :
    HObject fields bind R v ↔ AdmBody (.mk fields ff wild) v = true := by
  have hF := fun k => typedField_adm (hfields k) (ihr k) (iho k)
  cases v with
  | map keys f =>
    simp only [AdmBody, Bool.and_eq_true, valPresentT_req, objAdmV, decide_eq_true_eq]
    have hpres : (∀ k : {k // k ∈ fields}, (bind k).1 = true → k.1 ∈ keys) ↔
        (∀ k : {k // k ∈ fields}, ObjectSlot.isReq (ff k) = true → k.1 ∈ keys) :=
      forall_congr' fun k => by rw [(hF k).1]
    have hent : ∀ k : {k // k ∈ keys},
        (if h : k.1 ∈ fields then (bind ⟨k.1, h⟩).2 (f k) else ∃ T, R = some T ∧ T (f k)) ↔
        (entryP ⟨fields, fun k => AdmField (ff k)⟩ (AdmWild wild) k.1).any (· (f k)) = true := by
      intro k
      rcases Decidable.em (k.1 ∈ fields) with hk | hk
      · rw [dif_pos hk]
        simp only [entryP, MapOf.at, dif_pos hk]
        exact (hF ⟨k.1, hk⟩).2 _
      · rw [dif_neg hk]
        simp only [entryP, MapOf.at, dif_neg hk]
        cases hrest with
        | none => exact ⟨fun ⟨_, h, _⟩ => (nomatch h), fun h => (nomatch h)⟩
        | @some t' T' μ' hty =>
          simp only [AdmWild, Option.some.injEq, exists_eq_left']
          exact ihw t' rfl _ _ hty _
    constructor
    · rintro ⟨keys', f', heq, hreq, hall⟩
      cases heq
      exact ⟨hpres.mp hreq, fun k => (hent k).mp (hall k)⟩
    · rintro ⟨hreq, hall⟩
      exact ⟨keys, f, rfl, hpres.mpr hreq, fun k => (hent k).mpr (hall k)⟩
  | _ => simp [HObject, AdmBody]

/-- **`HSet` is the set row of `Adm`, under the set's obligations.** The element's held set is its
    admission, and a lawful element whose member is `S`, `N` or `B` writes a set exactly where it
    writes every element: (R) makes the element map injective, and the member law puts every
    element in one wire family. Without the obligations the row is narrower than `HSet`, because an
    element can collide two values or mix two members. -/
theorem hset_iff {t : Term} {T : Held} {μ} (hty : Typed t T μ) (hob : Obligations (.set t))
    (ih : ∀ w, T w ↔ Adm t w = true) (v : Value) : HSet T v ↔ Adm (.set t) v = true := by
  obtain ⟨hob', hse⟩ := hob
  have hl := (soundness hty hob').core
  cases hμ : (denote t).μ with
  | none => simp [SetElem, hμ] at hse
  | some μ₀ =>
  cases hsm : setMember μ₀ with
  | none => simp [SetElem, hμ, hsm] at hse
  | some μS =>
  have hw : ∀ x a, (denote t).e x = some a → a.member = μ₀ := fun _ _ h => hl.writes hμ h
  have hin : ∀ w, T w ↔ ((denote t).e w).isSome = true := fun w => (ih w).trans (Adm_exact t w)
  cases v with
  | strSet S =>
    show HSet T (.strSet S) ↔ (encSet (denote t) Value.str S).isSome = true
    simp only [HSet, Value.strSet.injEq, exists_eq_left', reduceCtorEq, false_and, exists_false,
      or_false]
    exact ⟨fun hall => encSet_isSome_of hl hsm (fun _ _ h => Value.str.inj h)
        (fun x hx => (hin _).mp (hall x hx)) (fun _ _ a h => hw _ a h),
      fun he x hx => by
        obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp he
        exact (hin _).mpr (encSet_elem ha x hx)⟩
  | numSet S =>
    show HSet T (.numSet S) ↔ (encSet (denote t) Value.num S).isSome = true
    simp only [HSet, Value.numSet.injEq, exists_eq_left', reduceCtorEq, false_and, exists_false,
      false_or, or_false]
    exact ⟨fun hall => encSet_isSome_of hl hsm (fun _ _ h => Value.num.inj h)
        (fun x hx => (hin _).mp (hall x hx)) (fun _ _ a h => hw _ a h),
      fun he x hx => by
        obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp he
        exact (hin _).mpr (encSet_elem ha x hx)⟩
  | binSet S =>
    show HSet T (.binSet S) ↔ (encSet (denote t) Value.bin S).isSome = true
    simp only [HSet, Value.binSet.injEq, exists_eq_left', reduceCtorEq, false_and, exists_false,
      false_or]
    exact ⟨fun hall => encSet_isSome_of hl hsm (fun _ _ h => Value.bin.inj h)
        (fun x hx => (hin _).mp (hall x hx)) (fun _ _ a h => hw _ a h),
      fun he x hx => by
        obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp he
        exact (hin _).mpr (encSet_elem ha x hx)⟩
  | _ => simp [HSet, Adm, setCodec]

/-- `HOpaque` is `opaque`'s admission: `opaque`'s held set is its write domain, and
    `opaq_T_identity` names that set. -/
theorem hopaque_adm (v : Value) : HOpaque v ↔ Adm .opaq v = true :=
  (opaq_T_identity v).symm

/-- A union's held set is the disjunction row of `Adm`. -/
theorem hunion_iff : ∀ {opts Ts μs}, TypedListμ opts Ts μs → (∀ t ∈ opts, AdmIff t) →
    ∀ v, HUnion Ts v ↔ AdmAny opts v = true
  -- by hand: `simp` closes `∃ T ∈ [], T v` through the classical `Nonempty` instance of `Held`
  | _, _, _, .nil, _, v => ⟨fun ⟨_, h, _⟩ => absurd h List.not_mem_nil, fun h => nomatch h⟩
  | _, _, _, @TypedListμ.cons t ts _ _ _ _ hty hs, ih, v => by
      have hi := hunion_iff hs (fun t' h => ih t' (List.mem_cons_of_mem _ h)) v
      have hT := ih _ List.mem_cons_self _ _ hty v
      simp only [HUnion, List.mem_cons, exists_eq_or_imp, AdmAny_cons, Bool.or_eq_true] at hi ⊢
      rw [hT, hi]

-- the shared `term_depth_wf` block has alternatives this theorem's goals do not use
set_option linter.unreachableTactic false in
/-- **(B): the held set is the admission, at every rule.** A derivable term whose obligations
    hold holds exactly the values it admits, so `T = dom(e)` by `Adm_exact`. `set` is the rule
    that reads the obligations (`hset_iff`); every other rule passes them to its subterms. -/
theorem typed_T_adm : ∀ {t T μ}, Typed t T μ → Obligations t → ∀ v, T v ↔ Adm t v = true
  | t, T, μ, h, hob, v => by
    cases h with
    | string => cases v <;> simp [Adm]
    | number => cases v <;> simp [Adm, inD]
    | boolean => cases v <;> simp [Adm]
    | binary => cases v <;> simp [Adm]
    | null => cases v <;> simp [Adm]
    | literal k x => cases k <;> cases v <;> simp [HLit, Adm, AdmLit, inL, GroundKind.toValue]
    | never => simp [HNever, Adm]
    | opaq => exact hopaque_adm v
    | var _ => simp [HNever, Adm]
    -- a `mu`'s held set is its write domain, which is its row
    | mu _ _ => exact Iff.rfl
    | @set t' T' μ' h' => exact hset_iff h' hob (typed_T_adm h' hob.1) v
    | @list pre Tpre sp Tsp suf Tsuf hp hs hf =>
      cases v with
      | arr vs =>
        simp only [HList, Adm, Value.arr.injEq, exists_eq_left']
        exact htupleL_iff hp hs hf
          (fun t' ht' _ _ hty w => typed_T_adm hty ((Obligations.list hob).1 t' ht') w)
          (fun t' ht' _ _ hty w => typed_T_adm hty ((Obligations.list hob).2.1 t' ht') w)
          (fun t' ht' _ _ hty w => typed_T_adm hty ((Obligations.list hob).2.2 t' ht') w) vs
      | _ => simp [HList, Adm]
    | @held t' I' μ' P f g h' =>
      exact (and_congr (typed_T_adm h' hob.1 (f v)) (Adm_exact P v).symm).trans
        Bool.and_eq_true_iff.symm
    | @refine t' T' μ' q h' =>
      show (T' v ∧ q.eval v = true) ↔ (Adm t' v && q.eval v) = true
      rw [Bool.and_eq_true, typed_T_adm h' hob v]
    | @object body bind R μs hfields hrest =>
      cases body with | mk fields ff wild =>
      simp only [Body.fields_mk, Body.at_mk, Body.wild_mk] at hfields hrest ⊢
      exact hobject_iff hfields
        (fun k t' he _ _ hty w => typed_T_adm hty (by have := hob.1 k; rw [he] at this; exact this) w)
        (fun k t' he _ _ hty w => typed_T_adm hty (by have := hob.1 k; rw [he] at this; exact this) w)
        hrest (fun t' he _ _ hty w => typed_T_adm hty (by have := hob.2; rw [he] at this; exact this) w) v
    | @union opts Ts μs h' =>
      rw [HUnion.eq_def] at *
      exact (hunion_iff h' (fun t' ht' _ _ hty w =>
          typed_T_adm hty ((Obligations.union hob).1 t' ht') w) v).trans
        (by rw [Adm_union])
termination_by t _ _ _ _ => Term.depth t
decreasing_by term_depth_wf


/-- A held set of the option judgements is some option's own. -/
theorem mem_typed_of_mem : ∀ {os : List Term} {Ts μs}, TypedListμ os Ts μs →
    ∀ T ∈ Ts, ∃ t ∈ os, ∃ μ, Typed t T μ
  | _, _, _, .nil, _, hT => nomatch hT
  | _, _, _, .cons hty hs, T, hT => by
    rcases List.mem_cons.mp hT with rfl | hT'
    · exact ⟨_, List.mem_cons_self, _, hty⟩
    · obtain ⟨t', ht', μ', hty'⟩ := mem_typed_of_mem hs T hT'
      exact ⟨t', List.mem_cons_of_mem _ ht', μ', hty'⟩

/-- A `Forall₂` relates every right element to some left one. -/
theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, List.Forall₂ R as bs → ∀ {b}, b ∈ bs → ∃ a ∈ as, R a b
  | _, _, .nil, _, hb => by simp at hb
  | _, _, .cons hr hrest, b, hb => by
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact ⟨_, List.mem_cons_self, hr⟩
      · obtain ⟨a, ha, hra⟩ := forall₂_mem_right hrest hb'
        exact ⟨a, List.mem_cons_of_mem _ ha, hra⟩

/-- **The meet keeps derivability.** Each survivor of a derivable union's meet is derivable. -/
theorem survivors {os zs ss : List Term} (hy : ∃ T μ, Typed (.union os) T μ)
    (hT : List.Forall₂ (fun t w => (∃ T μ, Typed t T μ) → ∃ T μ, Typed w T μ) os zs)
    (hs : ss.Sublist zs) : ∀ w ∈ ss, ∃ T μ, Typed w T μ := by
  obtain ⟨T, μ, hty⟩ := hy
  cases hty with
  | union hL =>
    intro w hw
    obtain ⟨t, ht, hr⟩ := forall₂_mem_right hT (hs.subset hw)
    obtain ⟨T', -, μ', hty'⟩ := TypedListμ.mem hL t ht
    exact hr ⟨T', μ', hty'⟩

end Calculus
