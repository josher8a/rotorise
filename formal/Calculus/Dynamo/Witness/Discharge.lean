import Calculus.Dynamo.Analysis.Meet

variable {α : Calculus.Table}

/-!
# A recursive schema

The host's recursive schema for JSON (`jsonTerm`) carried through `soundness`, with the refusals
of the guard pinned.
-/

namespace Calculus

/-! ## A recursive schema of the host, and the refusals of the guard

The host accepts `const json = union([string, array(lazy(() => json))])`. The model writes the
thunk that refers back to its own schema as a variable, and the schema as its binder. -/

/-- The host's schema for JSON: a string, or an array of the same schema. -/
def jsonTerm : Term := .mu (.union [.string, .array (.var 0)])

/-- **A binder whose variable reads the binder's own input is refused at construction**: no
    judgement types `mu (var 0)`, whose stages never grow. -/
theorem not_typed_unguarded_binder (T : Held) (μ : Option Member) :
    ¬ Typed α (.mu (.var 0)) T μ := by
  intro h
  cases h with
  | mu hg _ => exact absurd hg (by decide)

/-- **An option that reads the binder's input is refused**, as `union [var 0, string]`. -/
theorem guard_refuses_option_at_binder_input :
    (Term.mu (.union [.var 0, .string])).guarded = false := rfl

/-- **A `held` between the binder and its variable is refused**, although a container guards
    the variable: `f` can make the input deeper, so the stages need not agree. -/
theorem guard_refuses_held_on_path :
    (Term.mu (.array (.held false (.var 0) .opaq (.caller 0, false) []))).guarded = false := rfl

/-- A variable under a container is guarded, and so is an inner binder that reads an outer
    variable under a container. -/
theorem guard_accepts_container_path :
    jsonTerm.guarded = true ∧ (Term.mu (.array (.mu (.array (.var 1))))).guarded = true :=
  ⟨rfl, rfl⟩

/-- `jsonTerm` is derivable. -/
theorem typed_json : Typed α jsonTerm (fun v => (denote α jsonTerm).T v) none :=
  .mu rfl (.union (.cons (Typed.base _) (.cons (Typed.array (.var 0)) .nil)))

/-- `jsonTerm`'s options are compatible at every lawful stage: `Term.disjoint` keeps them apart
    whatever the variable denotes, and orthogonal lawful codecs are compatible. -/
theorem pairwiseCompat_json (c : Codec) (hc : Lawful c) :
    PairwiseCompat α [.string, .array (.var 0)] [c] := by
  have hd : Alg.Term.disjoint (S := dynSyn) Alg.pair0 Term.string (Term.array (.var 0)) = true := by rfl
  obtain ⟨hV, hA⟩ := Alg.disjoint_orthogonal (α := α) (β := dynTableA) hd
  have hx : Lawful (denote α .string [c]) := lawful_baseCodec .string
  have hy : Lawful (denote α (.array (.var 0)) [c]) := lawful_arrayCodec hc
  have hxy : Compat (denote α .string [c]) (denote α (.array (.var 0)) [c]) :=
    (Alg.compat_iff_agree hx hy).mpr
      ⟨Alg.agree_apart fun v => by
          have := hV [c] [c] (fun _ _ _ hp => nomatch hp) v
          rwa [Bool.eq_iff_iff.mpr (Alg.Adm_exact Term.string [c] v),
            Bool.eq_iff_iff.mpr (Alg.Adm_exact (Term.array (.var 0)) [c] v)] at this,
       Alg.agree_apart fun a => by
          have := hA [c] [c] (fun _ _ _ hp => nomatch hp) a
          rwa [Bool.eq_iff_iff.mpr (Alg.AdmA_exact Term.string [c] a),
            Bool.eq_iff_iff.mpr (Alg.AdmA_exact (Term.array (.var 0)) [c] a)] at this⟩
  exact forall_mem_pair (forall_mem_pair (compat_self _) hxy)
    (forall_mem_pair (Alg.compat_symm hx hy hxy) (compat_self _))

/-- `jsonTerm`'s obligations hold: the body owes compatibility at each stage, given that the
    stage before is lawful. -/
theorem obligations_json : Obligations α jsonTerm := fun _ hl =>
  ⟨⟨trivial, ⟨trivial, trivial, trivial⟩, trivial⟩, pairwiseCompat_json _ hl⟩

/-- **The host's recursive `jsonTerm` denotes a lawful codec.** -/
theorem lawful_json : Lawful (denote α jsonTerm) := soundness (α := α) typed_json obligations_json

/-- **`jsonTerm` is a fixed point**: it writes what one layer over `jsonTerm` writes. -/
theorem json_e_fix (v : Value) :
    (denote α jsonTerm).e v = (denote α (.union [.string, .array (.var 0)]) [denote α jsonTerm]).e v :=
  muCodec_fix (Alg.contractive_body (b := (.union [.string, .array (.var 0)] : Term)) rfl [])
    .host v

/-- `jsonTerm` writes a nested array through itself, and refuses an element it does not hold. -/
theorem json_vectors :
    (denote α jsonTerm).e (.arr [.str "a", .arr [.str "b"]]) = some (.l [.s "a", .l [.s "b"]])
    ∧ (denote α jsonTerm).e (.arr [.bool true]) = none
    ∧ (denote α jsonTerm).p (.l [.s "a", .l []]) = some (.arr [.str "a", .arr []]) :=
  ⟨rfl, rfl, rfl⟩

end Calculus
