import Calculus.Soundness

/-!
# The read gate of `refine`, a premise at two options, and a recursive schema

`refine`'s read-side gate, which `AdmA` reads, a premise checked at two options, and the host's
recursive schema for JSON (`jsonTerm`) carried through `soundness`, with the refusals of the
guard pinned.
-/

namespace Calculus

/-- **`refine`'s read-side gate**: decode with the base, then apply `q` to what comes out.

    The row this replaces was `admA (.refine t q) = admA t` — the predicate dropped — and
    the reason on record was that `q` tests the value a read *produces*, so no *syntactic*
    set of attributes bounds it. The premise is true and the conclusion does not follow, in
    exactly the way `number`'s and `opaq`'s `⊤`s did not follow: a row is not confined to
    syntax. It may call the denotation, and the denotation is what produces the value `q`
    tests. `(denote t).p a` is that value, or `none`; the gate is `q` of it.

    `AdmA`'s `refine` row is this function, which is why the row survived the retirement of
    the per-aspect tables it was first written for. -/
noncomputable def refineReads (t : Term) (q : Value → Bool) (a : Attr) : Bool :=
  match (denote t).p a with
  | some v => q v
  | none => false

/-- The gate, unfolded at a successful read. -/
theorem refineReads_some {t : Term} {q : Value → Bool} {a : Attr} {v : Value}
    (h : (denote t).p a = some v) : refineReads t q a = q v := by
  simp [refineReads, h]

/-- …and at a failed one. -/
theorem refineReads_none {t : Term} {q : Value → Bool} {a : Attr}
    (h : (denote t).p a = none) : refineReads t q a = false := by
  simp [refineReads, h]


/-! ## A premise at two options -/

/-- A premise of the form `∀ t ∈ [x, y], P t`, checked at the two options. -/
theorem forall_mem_pair {α : Type} {P : α → Prop} {x y : α} (hx : P x) (hy : P y) :
    ∀ z ∈ [x, y], P z := by
  intro z hz
  rcases List.mem_cons.mp hz with rfl | hz
  · exact hx
  · rcases List.mem_cons.mp hz with rfl | hz
    · exact hy
    · exact absurd hz (by simp)

/-! ## A recursive schema of the host, and the refusals of the guard

The host accepts `const json = union([string, array(lazy(() => json))])`. The model writes the
thunk that refers back to its own schema as a variable, and the schema as its binder. -/

/-- The host's schema for JSON: a string, or an array of the same schema. -/
def jsonTerm : Term := .mu (.union [.string, .array (.var 0)])

/-- **A binder whose variable reads the binder's own input is refused at construction**: no
    judgement types `mu (var 0)`, whose stages never grow. -/
theorem not_typed_unguarded_binder (T : Held) (μ : Option Member) :
    ¬ Typed (.mu (.var 0)) T μ := by
  intro h
  cases h with
  | mu hg _ => exact absurd hg (by decide)

/-- **An option that reads the binder's input is refused**, as `union [var 0, string]`. -/
theorem guard_refuses_option_at_binder_input :
    (Term.mu (.union [.var 0, .string])).guarded = false := rfl

/-- **A `held` between the binder and its variable is refused**, although a container guards
    the variable: `f` can make the input deeper, so the stages need not agree. -/
theorem guard_refuses_held_on_path :
    (Term.mu (.array (.held (.var 0) .opaq id id))).guarded = false := rfl

/-- A variable under a container is guarded, and so is an inner binder that reads an outer
    variable under a container. -/
theorem guard_accepts_container_path :
    jsonTerm.guarded = true ∧ (Term.mu (.array (.mu (.array (.var 1))))).guarded = true :=
  ⟨rfl, rfl⟩

/-- `jsonTerm` is derivable. -/
theorem typed_json : Typed jsonTerm (fun v => (denote jsonTerm).T v) none :=
  .mu rfl (.union (.cons (Typed.base _) (.cons (Typed.array (.var 0)) .nil)))

/-- `jsonTerm`'s options are compatible at every lawful stage: they are pinned to two kinds. -/
theorem pairwiseCompat_json (c : Codec) (hc : Lawful c) :
    PairwiseCompat [.string, .array (.var 0)] [c] := by
  have hA : denote (.array (.var 0)) [c] = arrayCodec c := (arrayCodec_eq_listCodec c).symm
  have h := compat_of_onKinds (os := [stringCodec, arrayCodec c]) (ks := [.string, .array])
    (forall_mem_pair lawful_stringCodec.core (lawful_arrayCodec hc).core)
    (.cons onKind_string (.cons (onKind_array c) .nil)) (by decide)
  have hs : denote .string [c] ∈ [stringCodec, arrayCodec c] := List.mem_cons_self
  have ha : denote (.array (.var 0)) [c] ∈ [stringCodec, arrayCodec c] := by
    rw [hA]; exact List.mem_cons_of_mem _ List.mem_cons_self
  exact forall_mem_pair (forall_mem_pair (h _ hs _ hs) (h _ hs _ ha))
    (forall_mem_pair (h _ ha _ hs) (h _ ha _ ha))

/-- `jsonTerm`'s obligations hold: the body owes compatibility at each stage, given that the
    stage before is lawful. -/
theorem obligations_json : Obligations jsonTerm := fun _ hl =>
  ⟨⟨trivial, ⟨trivial, trivial, trivial⟩, trivial⟩, fun s hs t ht => by
    rw [← denote_eq_alg, ← denote_eq_alg]; exact pairwiseCompat_json _ hl s hs t ht⟩

/-- **The host's recursive `jsonTerm` denotes a lawful codec.** -/
theorem lawful_json : Lawful (denote jsonTerm) := soundness typed_json obligations_json

/-- **`jsonTerm` is a fixed point**: it writes what one layer over `jsonTerm` writes. -/
theorem json_e_fix (v : Value) :
    (denote jsonTerm).e v = (denote (.union [.string, .array (.var 0)]) [denote jsonTerm]).e v :=
  muCodec_e_fix (contractive_body rfl []) v

/-- `jsonTerm` writes a nested array through itself, and refuses an element it does not hold. -/
theorem json_vectors :
    (denote jsonTerm).e (.arr [.str "a", .arr [.str "b"]]) = some (.l [.s "a", .l [.s "b"]])
    ∧ (denote jsonTerm).e (.arr [.bool true]) = none
    ∧ (denote jsonTerm).p (.l [.s "a", .l []]) = some (.arr [.str "a", .arr []]) :=
  ⟨rfl, rfl, rfl⟩

end Calculus
