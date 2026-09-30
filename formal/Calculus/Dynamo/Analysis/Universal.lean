import Calculus.Dynamo.Analysis.Meet

variable {α : Calculus.Table}

/-!
# `opaque` is the universal sum

`opaque` is the top of the admission lattice. `opaque` is not the unknown: the unknown carries
no information, and `opaque` admits each wire value. The normal form is one union over each
base and each container:

    opaque = union [string, boolean, binary, null, number,
                    array opaque, record opaque, set opaque]

These are the eight options of `opaqOptions`, one for one. `opaq` stays the name of the fixed
point. The union holds `opaq` under a container, so the union is a finite `Term`.

`set opaque` does not meet the DynamoDB set obligation (`SetElem`), because `opaque` names no
member. The unfolding is a statement of the algebra, and the obligation is the store's: a spelling
that meets it needs one set option per element member, `set string`, `set number` and
`set binary`, which is ten options. `denote .opaq` stays `muCodec opaqStep`, because a denotation of `opaq`
through the union recurses on a term that is not a subterm.

The unfolding is two theorems, one for each projection. `Adm_opaqUnfold` and
`AdmA_opaqUnfold` state that the union admits exactly what `opaque` admits. Each proof
reduces the union to the join of its options through the orthogonality certificate, then
reads each container case through `opaque` itself at the fixed point (`Ωe_arr` and the rest).
-/

namespace Calculus


/-- `opaque` unfolded one time. The recursion stays under a container, so the term is finite. -/
def opaqUnfold : Term :=
  .union [.string, .boolean, .binary, .null, .number,
    Term.array .opaq, Term.record .opaq, .set .opaq]

/-- The options of the unfolding are pairwise orthogonal. -/
theorem opaqUnfold_ok : unionOk (match opaqUnfold with | .union os => os | _ => []) = true := by
  decide

/-- `opaque` writes an array when `opaque` writes each element, at the element budget. -/
theorem Adm_opaq_arr (vs : List Value) :
    Adm α .opaq (.arr vs) = decide (∀ x ∈ vs, Adm α .opaq x = true) := by
  rw [Adm_opaq_eq, Ωe_arr, Option.isSome_map]
  refine Bool.eq_iff_iff.mpr ((traverse_isSome_iff _ vs).trans ?_)
  simp only [decide_eq_true_eq]
  exact Iff.rfl

/-- `opaque` writes a map when `opaque` writes each entry, at the entry budget. -/
theorem Adm_opaq_map (keys : Finset Name) (g : {k // k ∈ keys} → Value) :
    Adm α .opaq (.map keys g) = decide (∀ k, Adm α .opaq (g k) = true) := by
  rw [Adm_opaq_eq, Ωe_map, Option.isSome_map]
  refine Bool.eq_iff_iff.mpr (funImage_isSome_iff.trans ?_)
  simp only [decide_eq_true_eq]
  exact Iff.rfl

/-- **The unfolding lemma, write side.** `opaque` writes exactly the values that its
    unfolding writes. -/
theorem Adm_opaqUnfold (v : Value) : Adm α opaqUnfold v = Adm α .opaq v := by
  have hu : Adm α opaqUnfold v = AdmAny α (match opaqUnfold with | .union os => os | _ => []) v :=
    rfl
  rw [hu]
  cases v with
  | s s => rw [Adm_opaq_str]; rfl
  | bool b => rw [Adm_opaq_bool]; rfl
  | b b => rw [Adm_opaq_bin]; rfl
  | null => rw [Adm_opaq_null]; rfl
  | n d => rw [Adm_opaq_num]; rfl
  -- `set opaque` is `opaque`'s own set option, so the two rows are one expression
  | ss S =>
      rw [Adm_opaq_eq, Ωe_strSet]
      simp [opaqUnfold, AdmAny_cons, Adm_rows, Term.array, Term.record, inBase, setCodec, Alg.Codec.e]
      rfl
  | ns S =>
      rw [Adm_opaq_eq, Ωe_numSet]
      simp [opaqUnfold, AdmAny_cons, Adm_rows, Term.array, Term.record, inBase, setCodec, Alg.Codec.e]
      rfl
  | bs S =>
      rw [Adm_opaq_eq, Ωe_binSet]
      simp [opaqUnfold, AdmAny_cons, Adm_rows, Term.array, Term.record, inBase, setCodec, Alg.Codec.e]
      rfl
  | l vs =>
      rw [Adm_opaq_arr]
      simp [opaqUnfold, AdmAny_cons, Adm_rows, Term.array, Term.record, inBase, alignPL_spread, setCodec, Alg.Codec.e]
      exact decide_eq_decide.mpr Iff.rfl
  | m keys g =>
      -- the record's guard is vacuous over `∅`; a `simp` that unfolds the guard reaches
      -- `Finset.instIsEmpty`, so the guard stays folded and the fact is handed in
      have hp : valPresentT (S := dynSyn) ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)) keys = true :=
        decide_eq_true (fun k => absurd k.2 (Finset.notMem_empty k.1))
      rw [Adm_opaq_map]
      simp [opaqUnfold, AdmAny_cons, Adm_rows, Term.array, Term.record, inBase, objAdmV, entryP, MapOf.at, setCodec, Alg.Codec.e]
      exact fun _ => hp


/-- `opaque` reads a wire list when `opaque` reads each element, at the element budget. -/
theorem AdmA_opaq_l (as : List Attr) :
    AdmA α .opaq (.l as) = decide (∀ x ∈ as, AdmA α .opaq x = true) := by
  rw [AdmA_opaq_eq, Ωp_l, Option.isSome_map]
  refine Bool.eq_iff_iff.mpr ((traverse_isSome_iff _ as).trans ?_)
  simp only [decide_eq_true_eq]
  exact Iff.rfl

/-- `opaque` reads a wire map when `opaque` reads each entry, at the entry budget. -/
theorem AdmA_opaq_m (keys : Finset Name) (g : {k // k ∈ keys} → Attr) :
    AdmA α .opaq (.m keys g) = decide (∀ k, AdmA α .opaq (g k) = true) := by
  rw [AdmA_opaq_eq, Ωp_m, Option.isSome_map]
  refine Bool.eq_iff_iff.mpr (funImage_isSome_iff.trans ?_)
  simp only [decide_eq_true_eq]
  exact Iff.rfl

/-- **The unfolding lemma, read side.** `opaque` reads exactly the attributes that its
    unfolding reads. -/
theorem AdmA_opaqUnfold (a : Attr) : AdmA α opaqUnfold a = AdmA α .opaq a := by
  have hu : AdmA α opaqUnfold a
      = AdmAAny α (match opaqUnfold with | .union os => os | _ => []) a :=
    rfl
  rw [hu]
  cases a with
  | s x => rw [AdmA_opaq_str]; rfl
  | bool b => rw [AdmA_opaq_bool]; rfl
  | b x => rw [AdmA_opaq_bin]; rfl
  | null => rw [AdmA_opaq_null]; rfl
  | n x => rw [AdmA_opaq_num]; rfl
  | ss S =>
      rw [AdmA_opaq_eq, Ωp_ss]
      simp [opaqUnfold, AdmAAny, anyP, AdmA_rows, inBase, Term.array, Term.record, setCodec, Alg.Codec.p]
      rfl
  | bs S =>
      rw [AdmA_opaq_eq, Ωp_bs]
      simp [opaqUnfold, AdmAAny, anyP, AdmA_rows, inBase, Term.array, Term.record, setCodec, Alg.Codec.p]
      rfl
  | ns S =>
      rw [AdmA_opaq_eq, Ωp_ns]
      simp [opaqUnfold, AdmAAny, anyP, AdmA_rows, inBase, Term.array, Term.record, setCodec, Alg.Codec.p]
      rfl
  | l as =>
      rw [AdmA_opaq_l]
      simp [opaqUnfold, AdmAAny, anyP, AdmA_rows, inBase, Term.array,
        Term.record, alignPL_spread, setCodec, Alg.Codec.p]
      exact decide_eq_decide.mpr Iff.rfl
  | m keys g =>
      -- the record's guard stays folded, for the reason `Adm_opaqUnfold` gives
      have hp : valPresentT (S := dynSyn) ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)) keys = true :=
        decide_eq_true (fun k => absurd k.2 (Finset.notMem_empty k.1))
      rw [AdmA_opaq_m]
      simp [opaqUnfold, AdmAAny, anyP, AdmA_rows, inBase, Term.array,
        Term.record, objAdmV, entryP, MapOf.at, setCodec, Alg.Codec.p]
      exact fun _ => hp

/-- **`opaque` is total, write side.** `opaque` writes every value. -/
theorem opaq_total : ∀ v : Value, Adm α .opaq v = true
  | .str s => Adm_opaq_str s
  | .bool b => Adm_opaq_bool b
  | .bin b => Adm_opaq_bin b
  | .null => Adm_opaq_null
  | .num d => by rw [Adm_opaq_num]; rfl
  -- a scalar set is `HOpaque`, and `opaque` writes what `HOpaque` holds
  | .strSet S => by rw [Adm_opaq_eq]; exact hopaque_e (.strSet S fun s _ => .str s)
  | .numSet S => by rw [Adm_opaq_eq]; exact hopaque_e (.numSet S fun d _ => .num d)
  | .binSet S => by rw [Adm_opaq_eq]; exact hopaque_e (.binSet S fun b _ => .bin b)
  | .arr vs => by
      rw [Adm_opaq_arr]
      exact decide_eq_true (fun x hx =>
        have : Attr.depth x < Attr.depth (.l vs) := by
          have := Attr.depth_le_depthL hx; simp only [Attr.depth]; omega
        opaq_total x)
  | .map keys g => by
      rw [Adm_opaq_map]
      exact decide_eq_true (fun k =>
        have : Attr.depth (g k) < Attr.depth (.m keys g) := by
          have := Attr.depth_map_entry (f := g) k; omega
        opaq_total (g k))
termination_by v => Attr.depth v

/-- **`opaque` is total, read side.** `opaque` reads every attribute. -/
theorem opaqA_total : ∀ a : Attr, AdmA α .opaq a = true
  | .s x => AdmA_opaq_str x
  | .bool b => AdmA_opaq_bool b
  | .b x => AdmA_opaq_bin x
  | .null => AdmA_opaq_null
  | .n x => by rw [AdmA_opaq_num]; rfl
  -- `opaque` is a restriction of itself, so a wire set reads where each payload does
  | .ss S => by
      rw [AdmA_opaq_eq, Ωp_ss]
      exact (setCodec_isSome_of_sub (c := Ω) (fun _ _ _ h => h) .dual (.ss S)).mpr
        fun _ _ => rfl
  | .ns S => by
      rw [AdmA_opaq_eq, Ωp_ns]
      exact (setCodec_isSome_of_sub (c := Ω) (fun _ _ _ h => h) .dual (.ns S)).mpr
        fun _ _ => rfl
  | .bs S => by
      rw [AdmA_opaq_eq, Ωp_bs]
      exact (setCodec_isSome_of_sub (c := Ω) (fun _ _ _ h => h) .dual (.bs S)).mpr
        fun _ _ => rfl
  | .l as => by
      rw [AdmA_opaq_l]
      exact decide_eq_true (fun x hx =>
        have : Attr.depth x < Attr.depth (.l as) := by
          have := Attr.depth_le_depthL hx; simp only [Attr.depth]; omega
        opaqA_total x)
  | .m keys g => by
      rw [AdmA_opaq_m]
      exact decide_eq_true (fun k =>
        have : Attr.depth (g k) < Attr.depth (.m keys g) := by
          have := Attr.depth_map_entry (f := g) k; omega
        opaqA_total (g k))
termination_by a => Attr.depth a

end Calculus
