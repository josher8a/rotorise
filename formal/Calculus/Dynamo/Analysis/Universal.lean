import Calculus.Dynamo.Analysis.Meet

variable {α : Calculus.Table}

/-!
# `opaque` is the universal sum

`opaque` is the top of the admission lattice. `opaque` is not the unknown: the unknown carries
no information, and `opaque` admits each wire value. The normal form is one union over each
base and each container:

    opaque = union [string, boolean, binary, null, number,
                    array opaque, record opaque, set opaque]

`opaq` stays the name of the identity. The union holds `opaq` under a container, so the union
is a finite `Term`.

`set opaque` does not meet the DynamoDB set obligation (`SetElem`), because `opaque` names no
member. The unfolding is a statement of the algebra, and the obligation is the store's: a spelling
that meets it needs one set option per element member, `set string`, `set number` and
`set binary`, which is ten options.

The unfolding is two theorems, one for each projection. `Adm_opaqUnfold` and
`AdmA_opaqUnfold` state that the union admits exactly what `opaque` admits: every value, and
every attribute. Each proof reduces the union to the join of its options, and finds the one
option that admits each constructor.
-/

namespace Calculus


/-- `opaque` unfolded one time. The recursion stays under a container, so the term is finite. -/
def opaqUnfold : Term :=
  .union [.string, .boolean, .binary, .null, .number,
    Term.array .opaq, Term.record .opaq, .set .opaq]

/-- The options of the unfolding are pairwise orthogonal. -/
theorem opaqUnfold_ok : certAll (match opaqUnfold with | .union os => os | _ => []) = true := by
  decide

/-- **`opaque` is total, write side.** `opaque` writes every value. -/
theorem opaq_total (v : Value) : Adm α .opaq v = true := rfl

/-- **`opaque` is total, read side.** `opaque` reads every attribute. -/
theorem opaqA_total (a : Attr) : AdmA α .opaq a = true := rfl

/-- **The unfolding lemma, write side.** `opaque` writes exactly the values that its
    unfolding writes: every value. -/
theorem Adm_opaqUnfold (v : Value) : Adm α opaqUnfold v = Adm α .opaq v := by
  have hu : Adm α opaqUnfold v = AdmAny α (match opaqUnfold with | .union os => os | _ => []) v :=
    rfl
  rw [hu, opaq_total]
  cases v with
  | s _ | bool _ | b _ | null | n _ => rfl
  | ss S =>
      simp [opaqUnfold, AdmAny_cons, Adm_rows, Term.array, Term.record, inBase, setCodec, orient_rows, denote_opaq]
      exact Option.isSome_iff_exists.mpr ⟨_, setAt_Ω .host .string S⟩
  | ns S =>
      simp [opaqUnfold, AdmAny_cons, Adm_rows, Term.array, Term.record, inBase, setCodec, orient_rows, denote_opaq]
      exact Option.isSome_iff_exists.mpr ⟨_, setAt_Ω .host .number S⟩
  | bs S =>
      simp [opaqUnfold, AdmAny_cons, Adm_rows, Term.array, Term.record, inBase, setCodec, orient_rows, denote_opaq]
      exact Option.isSome_iff_exists.mpr ⟨_, setAt_Ω .host .binary S⟩
  | l vs =>
      simp [opaqUnfold, AdmAny_cons, Adm_rows, Term.array, Term.record, inBase, alignPL_spread, setCodec, orient_rows]
  | m keys g =>
      -- the record's guard is vacuous over `∅`; a `simp` that unfolds the guard reaches
      -- `Finset.instIsEmpty`, so the guard stays folded and the fact is handed in
      have hp : valPresentT (S := dynSyn) .host ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)) keys = true :=
        decide_eq_true (fun k _ => absurd k.2 (Finset.notMem_empty k.1))
      simp [opaqUnfold, AdmAny_cons, Adm_rows, Term.array, Term.record, inBase, objAdmV, entryP, MapOf.at, setCodec, orient_rows]
      exact hp

/-- **The unfolding lemma, read side.** `opaque` reads exactly the attributes that its
    unfolding reads: every attribute. -/
theorem AdmA_opaqUnfold (a : Attr) : AdmA α opaqUnfold a = AdmA α .opaq a := by
  have hu : AdmA α opaqUnfold a
      = AdmAAny α (match opaqUnfold with | .union os => os | _ => []) a :=
    rfl
  rw [hu, opaqA_total]
  cases a with
  | s _ | bool _ | b _ | null | n _ => rfl
  | ss S =>
      simp [opaqUnfold, AdmAAny, anyP, AdmA_rows, inBase, Term.array, Term.record, setCodec, orient_rows, denote_opaq]
      exact Option.isSome_iff_exists.mpr ⟨_, setAt_Ω .dual .string S⟩
  | bs S =>
      simp [opaqUnfold, AdmAAny, anyP, AdmA_rows, inBase, Term.array, Term.record, setCodec, orient_rows, denote_opaq]
      exact Option.isSome_iff_exists.mpr ⟨_, setAt_Ω .dual .binary S⟩
  | ns S =>
      simp [opaqUnfold, AdmAAny, anyP, AdmA_rows, inBase, Term.array, Term.record, setCodec, orient_rows, denote_opaq]
      exact Option.isSome_iff_exists.mpr ⟨_, setAt_Ω .dual .number S⟩
  | l as =>
      simp [opaqUnfold, AdmAAny, anyP, AdmA_rows, inBase, Term.array, Term.record, alignPL_spread, setCodec, orient_rows]
  | m keys g =>
      -- the record's guard stays folded, for the reason `Adm_opaqUnfold` gives
      have hp : valPresentT (S := dynSyn) .dual ∅ (fun k => absurd k.2 (Finset.notMem_empty k.1)) keys = true :=
        decide_eq_true (fun k _ => absurd k.2 (Finset.notMem_empty k.1))
      simp [opaqUnfold, AdmAAny, anyP, AdmA_rows, inBase, Term.array, Term.record, objAdmV, entryP, MapOf.at, setCodec, orient_rows]
      exact hp

end Calculus
