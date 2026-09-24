import Calculus.HeldSet
import Calculus.ExactV

/-!
# (B): the held set is the admission

A derivable term holds exactly the values that it admits (`typed_T_adm`), so the judgement's
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
        (match entryP ⟨fields, fun k => AdmField (ff k)⟩ (AdmWild wild) k.1 with
          | some P => P (f k) | none => false) = true := by
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

/-- A set base holds exactly what the base admits. -/
theorem setBase_held_adm (b : SetBase) (v : Value) : b.held v ↔ b.adm v = true := by
  cases b <;> cases v <;> simp [SetBase.held, SetBase.adm, inD]

/-- `HSet` is the set row of `Adm`. -/
theorem hset_iff (b : SetBase) (v : Value) : HSet b.held v ↔ Adm (.set b) v = true := by
  cases v with
  | strSet S => simp [HSet, Adm, setBase_held_adm]
  | numSet S => simp [HSet, Adm, setBase_held_adm]
  | binSet S => simp [HSet, Adm, setBase_held_adm]
  | _ => simp [HSet, Adm]

/-- An element of a list is no deeper than the list budget. -/
theorem depth_le_depthL {x : Value} : ∀ {vs : List Value}, x ∈ vs → Value.depth x ≤ Value.depthL vs
  | _ :: _, .head _ => by simp only [Value.depthL]; omega
  | _ :: _, .tail _ h => by have := depth_le_depthL h; simp only [Value.depthL]; omega

/-- `HOpaque` is `opaque`'s admission: each value is in `HOpaque`, and `opaque` writes each value. -/
theorem hopaque_adm (v : Value) : HOpaque v ↔ Adm .opaq v = true := by
  constructor
  · intro h
    induction h with
    | str s => show ((opaqCodec 1).e (.str s)).isSome = true; rw [opaqCodec_e_str 0]; simp [stringCodec]
    | bool b => show ((opaqCodec 1).e (.bool b)).isSome = true; rw [opaqCodec_e_bool 0]; simp [booleanCodec]
    | bin b => show ((opaqCodec 1).e (.bin b)).isSome = true; rw [opaqCodec_e_bin 0]; simp [binaryCodec]
    | null => show ((opaqCodec 1).e .null).isSome = true; rw [opaqCodec_e_null 0]; simp [nullCodec]
    | num d => show ((opaqCodec 1).e (.num d)).isSome = true; rw [opaqCodec_e_num 0]; simp [numberCodec]
    | strSet S _ _ =>
      show ((opaqCodec 2).e (.strSet S)).isSome = true
      rw [opaqCodec_e_strSet 1]
      show (encSet (opaqCodec 1) Value.str S).isSome = true
      rw [encSet_congr (d := SetBase.string.elem) (fun x _ => opaqCodec_e_str 0 x)]
      exact (Adm_exact (.set .string) (.strSet S)).mp (by simp [Adm, SetBase.adm])
    | numSet S _ _ =>
      show ((opaqCodec 2).e (.numSet S)).isSome = true
      rw [opaqCodec_e_numSet 1]
      show (encSet (opaqCodec 1) Value.num S).isSome = true
      rw [encSet_congr (d := SetBase.number.elem) (fun x _ => opaqCodec_e_num 0 x)]
      exact (Adm_exact (.set .number) (.numSet S)).mp (by simp [Adm, SetBase.adm, inD])
    | binSet S _ _ =>
      show ((opaqCodec 2).e (.binSet S)).isSome = true
      rw [opaqCodec_e_binSet 1]
      show (encSet (opaqCodec 1) Value.bin S).isSome = true
      rw [encSet_congr (d := SetBase.binary.elem) (fun x _ => opaqCodec_e_bin 0 x)]
      exact (Adm_exact (.set .binary) (.binSet S)).mp (by simp [Adm, SetBase.adm])
    | arr vs _ ih =>
      show ((opaqCodec (Value.depthL vs + 1)).e (.arr vs)).isSome = true
      rw [opaqCodec_e_arr]
      show ((traverse (opaqCodec (Value.depthL vs)).e vs).map Attr.l).isSome = true
      rw [Option.isSome_map, traverse_isSome_iff]
      intro x hx
      have := ih x hx
      change ((opaqCodec (Value.depth x)).e x).isSome = true at this
      rwa [opaq_e_agree x _ _ (Nat.le_refl _) (depth_le_depthL hx)] at this
    | map keys f _ ih =>
      obtain ⟨n, hn⟩ : ∃ n, Value.depth (.map keys f) = n + 1 := ⟨_, rfl⟩
      show ((opaqCodec (Value.depth (.map keys f))).e _).isSome = true
      rw [hn, opaqCodec_e_map]
      show ((funImage fun k => (opaqCodec n).e (f k)).map (Attr.m keys)).isSome = true
      rw [Option.isSome_map, funImage_isSome_iff]
      intro k
      have := ih k
      have hd := Value.depth_map_entry (f := f) k
      change ((opaqCodec (Value.depth (f k))).e (f k)).isSome = true at this
      rwa [opaq_e_agree (f k) (Value.depth (f k)) n (Nat.le_refl _) (by omega)] at this
  · intro h
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp h
    exact (opaq_T_identity v).mp (carrier_opaqCodecω.domE ha)

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
/-- **(B): the held set is the admission, at every rule.** A derivable term holds exactly the
    values it admits, so `T = dom(e)` by `Adm_exact`. -/
theorem typed_T_adm : ∀ {t T μ}, Typed t T μ → ∀ v, T v ↔ Adm t v = true
  | t, T, μ, h, v => by
    cases h with
    | string => cases v <;> simp [Adm]
    | number => cases v <;> simp [Adm, inD]
    | boolean => cases v <;> simp [Adm]
    | binary => cases v <;> simp [Adm]
    | null => cases v <;> simp [Adm]
    | literal k x => cases k <;> cases v <;> simp [HLit, Adm, AdmLit, inL, GroundKind.toValue]
    | never => simp [HNever, Adm]
    | opaq => exact hopaque_adm v
    | set b => exact hset_iff b v
    | @list pre Tpre sp Tsp suf Tsuf hp hs hf =>
      cases v with
      | arr vs =>
        simp only [HList, Adm, Value.arr.injEq, exists_eq_left']
        exact htupleL_iff hp hs hf
          (fun t' _ _ _ hty w => typed_T_adm hty w)
          (fun t' _ _ _ hty w => typed_T_adm hty w)
          (fun t' _ _ _ hty w => typed_T_adm hty w) vs
      | _ => simp [HList, Adm]
    | @held t' I' μ' P f g h' =>
      exact (and_congr (typed_T_adm h' (f v)) (Adm_exact P v).symm).trans
        Bool.and_eq_true_iff.symm
    | @refine t' T' μ' q h' =>
      show (T' v ∧ q.eval v = true) ↔ (Adm t' v && q.eval v) = true
      rw [Bool.and_eq_true, typed_T_adm h' v]
    | @lazy t' T' μ' h' => exact typed_T_adm h' v
    | @object body bind R μs hfields hrest =>
      cases body with | mk fields ff wild =>
      simp only [Body.fields_mk, Body.at_mk, Body.wild_mk] at hfields hrest ⊢
      exact hobject_iff hfields
        (fun k t' _ _ _ hty w => typed_T_adm hty w)
        (fun k t' _ _ _ hty w => typed_T_adm hty w)
        hrest (fun t' _ _ _ hty w => typed_T_adm hty w) v
    | @union opts Ts μs h' =>
      rw [HUnion.eq_def] at *
      exact (hunion_iff h' (fun t' _ _ _ hty w => typed_T_adm hty w) v).trans
        (by rw [Adm_union, selOptV_eq_AdmAny])
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
