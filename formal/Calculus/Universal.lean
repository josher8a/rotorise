import Calculus.Meet

/-!
# `opaque` is the universal sum

`opaque` is the top of the admission lattice. `opaque` is not the unknown: the unknown carries
no information, and `opaque` admits each wire value. The normal form is one union over each
base and each container:

    opaque = union [string, boolean, binary, null, number,
                    array (lazy opaque), record (lazy opaque),
                    set string, set number, set binary]

`opaq` stays the name of the fixed point. The union holds `opaq` under `lazy`, so the union is
a finite `Term`, and no constructor is necessary. `denote .opaq` stays `opaqCodecω`,
because a denotation of `opaq` through the union recurses on a term that is not a subterm.

The unfolding is two theorems, one for each projection. `Adm_opaqUnfold` and
`AdmA_opaqUnfold` state that the union admits exactly what `opaque` admits. Each proof
reduces the union to the join of its options through the orthogonality certificate, then
moves each container case to the budget of its elements through the stabilization lemmas.
-/

namespace Calculus


/-- `opaque` unfolded one time. The recursion stays under `lazy`, so the term is finite. -/
def opaqUnfold : Term :=
  .union [.string, .boolean, .binary, .null, .number,
    Term.array (.lazy .opaq), Term.record (.lazy .opaq), .set .string, .set .number, .set .binary]

/-- `opaque` writes each element of a string set as the string base writes it. -/
theorem encSet_opaq_str (n : Nat) (S : NEFinset String) :
    encSet (opaqCodec (n+1)) Value.str S = encSet SetBase.string.elem Value.str S := by
  simp only [encSet, show ∀ x : String, (opaqCodec (n+1)).e (Value.str x)
    = SetBase.string.elem.e (Value.str x) from fun x => by
      rw [opaqCodec_e_str]; rfl]

/-- `opaque` writes each element of a byte-string set as the binary base writes it. -/
theorem encSet_opaq_bin (n : Nat) (S : NEFinset Bytes) :
    encSet (opaqCodec (n+1)) Value.bin S = encSet SetBase.binary.elem Value.bin S := by
  simp only [encSet, show ∀ x : Bytes, (opaqCodec (n+1)).e (Value.bin x)
    = SetBase.binary.elem.e (Value.bin x) from fun x => by
      rw [opaqCodec_e_bin]; rfl]

/-- `opaque` writes each element of a number set as the number base writes it. -/
theorem encSet_opaq_num (n : Nat) (S : NEFinset WFNumeral) :
    encSet (opaqCodec (n+1)) Value.num S = encSet SetBase.number.elem Value.num S := by
  simp only [encSet, show ∀ x : WFNumeral, (opaqCodec (n+1)).e (Value.num x)
    = SetBase.number.elem.e (Value.num x) from fun x => by
      rw [opaqCodec_e_num]; rfl]

/-- The options of the unfolding are pairwise orthogonal. -/
theorem opaqUnfold_ok : unionOk (match opaqUnfold with | .union os => os | _ => []) = true := by
  decide

/-- A list with no prefix and no suffix admits a value when the spread admits each element. -/
theorem alignPL_spread (P : VP) (vs : List Value) :
    alignPL [] (some P) [] vs = decide (∀ x ∈ vs, P x = true) := by
  simp only [alignPL, List.length_nil, Nat.sub_zero, List.take_length, List.drop_length, zipP,
    Bool.and_true]
  induction vs with
  | nil => rfl
  | cons x xs ih => simp [alignP, ih]

/-- `opaque` writes an array when `opaque` writes each element, at the element budget. -/
theorem Adm_opaq_arr (vs : List Value) :
    Adm .opaq (.arr vs) = decide (∀ x ∈ vs, Adm .opaq x = true) := by
  rw [Adm_opaq_eq, show Value.depth (.arr vs) = Value.depthL vs + 1 from rfl, opaqCodec_e_arr]
  show ((traverse (opaqCodec (Value.depthL vs)).e vs).map Attr.l).isSome = _
  rw [Option.isSome_map]
  refine Bool.eq_iff_iff.mpr ((traverse_isSome_iff _ vs).trans ?_)
  simp only [decide_eq_true_eq]
  refine forall₂_congr fun x hx => ?_
  rw [Adm_opaq_eq, opaq_e_agree x _ _ (depth_le_depthL hx) (Nat.le_refl _)]

/-- `opaque` writes a map when `opaque` writes each entry, at the entry budget. -/
theorem Adm_opaq_map (keys : Finset Name) (g : {k // k ∈ keys} → Value) :
    Adm .opaq (.map keys g) = decide (∀ k, Adm .opaq (g k) = true) := by
  rw [Adm_opaq_eq]
  obtain ⟨n, hn⟩ : ∃ n, Value.depth (.map keys g) = n + 1 :=
    ⟨_, rfl⟩
  rw [hn, opaqCodec_e_map]
  show ((funImage fun k => (opaqCodec n).e (g k)).map (Attr.m keys)).isSome = _
  rw [Option.isSome_map]
  refine Bool.eq_iff_iff.mpr (funImage_isSome_iff.trans ?_)
  simp only [decide_eq_true_eq]
  refine forall_congr' fun k => ?_
  have := Value.depth_map_entry (f := g) k
  rw [Adm_opaq_eq, opaq_e_agree (g k) _ _ (by omega) (Nat.le_refl _)]

/-- **The unfolding lemma, write side.** `opaque` writes exactly the values that its
    unfolding writes. -/
theorem Adm_opaqUnfold (v : Value) : Adm opaqUnfold v = Adm .opaq v := by
  have hu : Adm opaqUnfold v = AdmAny (match opaqUnfold with | .union os => os | _ => []) v :=
    selOptV_eq_AdmAny _ v
  rw [hu]
  cases v with
  | str s => rw [Adm_opaq_str]; rfl
  | bool b => rw [Adm_opaq_bool]; rfl
  | bin b => rw [Adm_opaq_bin]; rfl
  | null => rw [Adm_opaq_null]; rfl
  | num d => rw [Adm_opaq_num]; rfl
  | strSet S =>
      rw [Adm_opaq_eq, show Value.depth (.strSet S) = (1 : Nat) + 1 from rfl,
        opaqCodec_e_strSet]
      show _ = (encSet (opaqCodec (0+1)) Value.str S).isSome
      rw [encSet_opaq_str]
      rw [(encSet_base_iff SetBase.string (fun _ _ h => Value.str.inj h) S).mpr
        (fun _ _ => rfl)]
      simp [opaqUnfold, AdmAny_cons, Adm, AdmBody, Term.array, Term.record,
        inD, SetBase.adm]
  | numSet S =>
      rw [Adm_opaq_eq, show Value.depth (.numSet S) = (1 : Nat) + 1 from rfl,
        opaqCodec_e_numSet]
      show _ = (encSet (opaqCodec (0+1)) Value.num S).isSome
      rw [encSet_opaq_num, (encSet_base_iff SetBase.number (fun _ _ h => Value.num.inj h) S).mpr
        (fun _ _ => rfl)]
      simp [opaqUnfold, AdmAny_cons, Adm, AdmBody, Term.array, Term.record, inD, SetBase.adm]
  | binSet S =>
      rw [Adm_opaq_eq, show Value.depth (.binSet S) = (1 : Nat) + 1 from rfl,
        opaqCodec_e_binSet]
      show _ = (encSet (opaqCodec (0+1)) Value.bin S).isSome
      rw [encSet_opaq_bin, (encSet_base_iff SetBase.binary (fun _ _ h => Value.bin.inj h) S).mpr
        (fun _ _ => rfl)]
      simp [opaqUnfold, AdmAny_cons, Adm, AdmBody, Term.array, Term.record, inD,
        SetBase.adm]
  | arr vs =>
      rw [Adm_opaq_arr]
      simp [opaqUnfold, AdmAny_cons, Adm, AdmBody, Term.array, Term.record, inD,
        AdmOptT, alignPL_spread]
      exact decide_eq_decide.mpr Iff.rfl
  | map keys g =>
      -- the record's guard is vacuous over `∅`; a `simp` that unfolds the guard reaches
      -- `Finset.instIsEmpty`, so the guard stays folded and the fact is handed in
      have hp : valPresentT ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)) keys = true :=
        decide_eq_true (fun k => absurd k.2 (Finset.notMem_empty k.1))
      rw [Adm_opaq_map]
      simp [opaqUnfold, AdmAny_cons, Adm, AdmBody, Term.array, Term.record, inD,
        AdmWild, objAdmV, entryP, MapOf.at]
      exact fun _ => hp


/-- `alignPL_spread` on the read side. -/
theorem alignPAL_spread (P : AP) (as : List Attr) :
    alignPAL [] (some P) [] as = decide (∀ x ∈ as, P x = true) := by
  simp only [alignPAL, List.length_nil, Nat.sub_zero, List.take_length, List.drop_length, zipPA,
    Bool.and_true]
  induction as with
  | nil => rfl
  | cons x xs ih => simp [alignPA, ih]

/-- `depth_le_depthL` on the read side. -/
theorem depth_le_depthLA {x : Attr} : ∀ {as : List Attr}, x ∈ as → Attr.depth x ≤ Attr.depthL as
  | _ :: _, .head _ => by simp only [Attr.depthL]; omega
  | _ :: _, .tail _ h => by have := depth_le_depthLA h; simp only [Attr.depthL]; omega

/-- `opaque` reads a wire list when `opaque` reads each element, at the element budget. -/
theorem AdmA_opaq_l (as : List Attr) :
    AdmA .opaq (.l as) = decide (∀ x ∈ as, AdmA .opaq x = true) := by
  rw [AdmA_opaq_eq, show Attr.depth (.l as) = Attr.depthL as + 1 from rfl, opaqCodec_p_l]
  show ((traverse (opaqCodec (Attr.depthL as)).p as).map Value.arr).isSome = _
  rw [Option.isSome_map]
  refine Bool.eq_iff_iff.mpr ((traverse_isSome_iff _ as).trans ?_)
  simp only [decide_eq_true_eq]
  refine forall₂_congr fun x hx => ?_
  rw [AdmA_opaq_eq, opaq_p_agree x _ _ (depth_le_depthLA hx) (Nat.le_refl _)]

/-- `opaque` reads a wire map when `opaque` reads each entry, at the entry budget. -/
theorem AdmA_opaq_m (keys : Finset Name) (g : {k // k ∈ keys} → Attr) :
    AdmA .opaq (.m keys g) = decide (∀ k, AdmA .opaq (g k) = true) := by
  rw [AdmA_opaq_eq]
  obtain ⟨n, hn⟩ : ∃ n, Attr.depth (.m keys g) = n + 1 := ⟨_, rfl⟩
  rw [hn, opaqCodec_p_m]
  show ((funImage fun k => (opaqCodec n).p (g k)).map (Value.map keys)).isSome = _
  rw [Option.isSome_map]
  refine Bool.eq_iff_iff.mpr (funImage_isSome_iff.trans ?_)
  simp only [decide_eq_true_eq]
  refine forall_congr' fun k => ?_
  have := Attr.depth_map_entry (f := g) k
  rw [AdmA_opaq_eq, opaq_p_agree (g k) _ _ (by omega) (Nat.le_refl _)]

/-- A set base's row is its codec's read domain, as a `Bool`. -/
theorem AdmA_set_eq (b : SetBase) (a : Attr) :
    AdmA (.set b) a = ((setCodec b.elem).p a).isSome :=
  Bool.eq_iff_iff.mpr (ExactA_set b a)

/-- **The unfolding lemma, read side.** `opaque` reads exactly the attributes that its
    unfolding reads. -/
theorem AdmA_opaqUnfold (a : Attr) : AdmA opaqUnfold a = AdmA .opaq a := by
  have hu : AdmA opaqUnfold a
      = AdmAAny (match opaqUnfold with | .union os => os | _ => []) a :=
    selOptA_eq_AdmAAny _ a
  rw [hu]
  cases a with
  | s x => rw [AdmA_opaq_str]; rfl
  | bool b => rw [AdmA_opaq_bool]; rfl
  | b x => rw [AdmA_opaq_bin]; rfl
  | null => rw [AdmA_opaq_null]; rfl
  | n x => rw [AdmA_opaq_num]; rfl
  | ss S =>
      have he : (setCodec (opaqCodec 1)).p (.ss S) = (setCodec SetBase.string.elem).p (.ss S) := by
        simp only [setCodec, decSet, show ∀ x : String, (opaqCodec (0+1)).p (Attr.s x)
          = SetBase.string.elem.p (Attr.s x) from fun x => by rw [opaqCodec_p_s]; rfl]
      rw [AdmA_opaq_eq, show Attr.depth (.ss S) = (1 : Nat) + 1 from rfl, opaqCodec_p_ss, he,
        ← AdmA_set_eq]
      rfl
  | bs S =>
      have he : (setCodec (opaqCodec 1)).p (.bs S) = (setCodec SetBase.binary.elem).p (.bs S) := by
        simp only [setCodec, decSet, show ∀ x : Bytes, (opaqCodec (0+1)).p (Attr.b x)
          = SetBase.binary.elem.p (Attr.b x) from fun x => by rw [opaqCodec_p_b]; rfl]
      rw [AdmA_opaq_eq, show Attr.depth (.bs S) = (1 : Nat) + 1 from rfl, opaqCodec_p_bs, he,
        ← AdmA_set_eq]
      rfl
  | ns S =>
      rw [AdmA_opaq_eq, show Attr.depth (.ns S) = (1 : Nat) + 1 from rfl, opaqCodec_p_ns]
      have he : (setCodec (opaqCodec 1)).p (.ns S)
          = (setCodec SetBase.number.elem).p (.ns S) := by
        simp only [setCodec, decSet, show ∀ x : WFNumeral, (opaqCodec (0+1)).p (Attr.n x)
          = SetBase.number.elem.p (Attr.n x) from fun x => by rw [opaqCodec_p_n]; rfl]
      rw [he, ← AdmA_set_eq]
      simp [opaqUnfold, AdmA, AdmASet, AdmABody, Term.array, Term.record]
  | l as =>
      rw [AdmA_opaq_l]
      simp [opaqUnfold, AdmAAny, anyPA, AdmA, AdmABody, AdmASet, Term.array,
        Term.record, AdmAOptT, alignPAL_spread]
      exact decide_eq_decide.mpr Iff.rfl
  | m keys g =>
      -- the record's guard stays folded, for the reason `Adm_opaqUnfold` gives
      have hp : reqPresentT ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)) keys = true :=
        decide_eq_true (fun k => absurd k.2 (Finset.notMem_empty k.1))
      rw [AdmA_opaq_m]
      simp [opaqUnfold, AdmAAny, anyPA, AdmA, AdmABody, AdmASet, Term.array,
        Term.record, AdmAWild, objAdmA, entryPA, MapOf.at]
      exact fun _ => hp

/-- **`opaque` is total, write side.** `opaque` writes every value. -/
theorem opaq_total : ∀ v : Value, Adm .opaq v = true
  | .str s => Adm_opaq_str s
  | .bool b => Adm_opaq_bool b
  | .bin b => Adm_opaq_bin b
  | .null => Adm_opaq_null
  | .num d => by rw [Adm_opaq_num]; rfl
  | .strSet S => by
      rw [← Adm_opaqUnfold, show Adm opaqUnfold _ = AdmAny _ _ from
        selOptV_eq_AdmAny _ _]
      simp [opaqUnfold, Adm, AdmBody, Term.array, Term.record, SetBase.adm, inD]
  | .numSet S => by
      rw [← Adm_opaqUnfold, show Adm opaqUnfold _ = AdmAny _ _ from
        selOptV_eq_AdmAny _ _]
      simp [opaqUnfold, Adm, AdmBody, Term.array, Term.record, SetBase.adm, inD]
  | .binSet S => by
      rw [← Adm_opaqUnfold, show Adm opaqUnfold _ = AdmAny _ _ from
        selOptV_eq_AdmAny _ _]
      simp [opaqUnfold, Adm, AdmBody, Term.array, Term.record, SetBase.adm, inD]
  | .arr vs => by
      rw [Adm_opaq_arr]
      exact decide_eq_true (fun x hx =>
        have : Value.depth x < Value.depth (.arr vs) := by
          have := depth_le_depthL hx; simp only [Value.depth]; omega
        opaq_total x)
  | .map keys g => by
      rw [Adm_opaq_map]
      exact decide_eq_true (fun k =>
        have : Value.depth (g k) < Value.depth (.map keys g) := by
          have := Value.depth_map_entry (f := g) k; omega
        opaq_total (g k))
termination_by v => Value.depth v

/-- **`opaque` is total, read side.** `opaque` reads every attribute. -/
theorem opaqA_total : ∀ a : Attr, AdmA .opaq a = true
  | .s x => AdmA_opaq_str x
  | .bool b => AdmA_opaq_bool b
  | .b x => AdmA_opaq_bin x
  | .null => AdmA_opaq_null
  | .n x => by rw [AdmA_opaq_num]; rfl
  | .ss S => by
      rw [← AdmA_opaqUnfold, show AdmA opaqUnfold _ = AdmAAny _ _ from
        selOptA_eq_AdmAAny _ _]
      simp [opaqUnfold, AdmA, AdmABody, AdmASet, Term.array, Term.record]
  | .ns S => by
      rw [← AdmA_opaqUnfold, show AdmA opaqUnfold _ = AdmAAny _ _ from
        selOptA_eq_AdmAAny _ _]
      simp [opaqUnfold, AdmA, AdmABody, AdmASet, Term.array, Term.record]
      obtain ⟨x₀, hx₀⟩ := S.2
      exact decSet_isSome_num hx₀ rfl (fun _ _ => rfl)
        (fun x₁ _ x₂ _ y h₁ h₂ => by
          simp only [numberCodec, Option.bind_some, vNum, Option.some.injEq] at h₁ h₂
          exact h₁.trans h₂.symm)
  | .bs S => by
      rw [← AdmA_opaqUnfold, show AdmA opaqUnfold _ = AdmAAny _ _ from
        selOptA_eq_AdmAAny _ _]
      simp [opaqUnfold, AdmA, AdmABody, AdmASet, Term.array, Term.record]
  | .l as => by
      rw [AdmA_opaq_l]
      exact decide_eq_true (fun x hx =>
        have : Attr.depth x < Attr.depth (.l as) := by
          have := depth_le_depthLA hx; simp only [Attr.depth]; omega
        opaqA_total x)
  | .m keys g => by
      rw [AdmA_opaq_m]
      exact decide_eq_true (fun k =>
        have : Attr.depth (g k) < Attr.depth (.m keys g) := by
          have := Attr.depth_map_entry (f := g) k; omega
        opaqA_total (g k))
termination_by a => Attr.depth a

end Calculus
