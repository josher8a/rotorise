import Calculus.Dynamo.Lang.ScopeSound

/-!
# A recursive schema, as a closed codec

The host's recursive schema for JSON as a closed codec (`jsonClosed`), carried through
`Closed.sound`, and the shapes that have no closed codec.

A closed codec names an entry above every guard only below its own position, and below a wall
it names no entry of its own scope: the type of a scope term holds no other leaf. The flat graph
of a codec has a form as a DAG of scopes exactly where `dagGuardB` accepts it
(`dagGuardB_iff_dsys`). So a shape that the guard of a binder refuses is a graph that `dagGuardB`
refuses, and no closed codec has that graph as its graph form.
-/

namespace Calculus

variable {α : Table}

/-- The term of the one entry of the host's schema for JSON: a string, or an array of the entry. -/
def jsonBody : Scoped.Term 0 1 0 :=
  Scoped.Term.union [Scoped.Term.string, Scoped.Term.array (Scoped.Term.ref 0)]

/-- The host's schema for JSON, as a closed codec of one entry. -/
def jsonClosed : Closed := Closed.one jsonBody

/-- The entry of `jsonClosed` is typed at every environment: each operation has a rule. -/
theorem typed_jsonBody (τ : (s : Bool) → Alg.TableAt dynSig s) (κ : Fin 0 → Codec)
    (ρw : Fin 1 → Codec) (ρk : Fin 0 → Codec) : ∃ T μ, Alg.Scoped.Typed τ κ ρw ρk jsonBody T μ := by
  obtain ⟨T1, μ1, h1⟩ : ∃ T μ, Alg.Scoped.Typed τ κ ρw ρk Scoped.Term.string T μ :=
    ⟨_, _, Alg.Scoped.Typed.node (B := dynSig) (o := .prim (Ground.base .string)) (T := Empty.elim) (μ := Empty.elim) (fun p => p.elim) rfl⟩
  obtain ⟨T2, μ2, h2⟩ : ∃ T μ,
      Alg.Scoped.Typed τ κ ρw ρk (Scoped.Term.array (Scoped.Term.ref 0)) T μ :=
    ⟨_, _, Alg.Scoped.Typed.node (B := dynSig) (o := .list 0 1 0) (T := fun _ => (ρw 0).T) (μ := fun _ => (ρw 0).μ)
      (fun p => match p with
        | .inl p => p.elim0
        | .inr (.inl _) => .ref ⟨0, Nat.one_pos⟩
        | .inr (.inr p) => p.elim0) rfl⟩
  exact ⟨_, _, Alg.Scoped.Typed.node (B := dynSig) (o := .union 2) (T := [T1, T2].get) (μ := [μ1, μ2].get)
    (fun p => match p with
      | ⟨0, _⟩ => h1
      | ⟨1, _⟩ => h2) rfl⟩

/-- `jsonClosed` is typed. -/
theorem Closed.typed_json : jsonClosed.Typed α :=
  ⟨trivial, fun i => match i with | ⟨0, _⟩ => typed_jsonBody _ _ _ _⟩

/-- **A string and an array are compatible**, whatever the element: no attribute and no value is
    on both. -/
theorem compat_string_array {x : Codec} (hx : Lawful x) :
    Compat (groundCodec (.base .string)) (arrayCodec x) := by
  refine (Alg.compat_iff_agree (lawful_groundCodec _) (lawful_arrayCodec hx)).mpr
    ⟨Alg.agree_apart fun v => ?_, Alg.agree_apart fun a => ?_⟩
  · cases v <;> rfl
  · cases a <;> rfl

/-- The entry of `jsonClosed` meets its obligations at every environment whose entry is lawful:
    its two options are compatible. -/
theorem obligations_jsonBody (τ : (s : Bool) → Alg.TableAt dynSig s) (κ : Fin 0 → Codec)
    (ρw : Fin 1 → Codec) (ρk : Fin 0 → Codec) (hw : Lawful (ρw 0)) :
    Alg.Scoped.Obligations τ κ ρw ρk jsonBody := by
  have hs := compat_string_array hw
  have hl : Lawful (arrayCodec (ρw 0)) := lawful_arrayCodec hw
  refine ⟨fun p => ?_, fun p q => ?_⟩
  · match p with
    | ⟨0, _⟩ => exact ⟨fun p => p.elim, trivial⟩
    | ⟨1, _⟩ =>
      refine ⟨fun p => ?_, trivial⟩
      match p with
      | .inl p => exact p.elim0
      | .inr (.inl _) => trivial
      | .inr (.inr p) => exact p.elim0
  · match p, q with
    | ⟨0, _⟩, ⟨0, _⟩ => exact fun _ _ hp _ => hp
    | ⟨0, _⟩, ⟨1, _⟩ => exact hs
    | ⟨1, _⟩, ⟨0, _⟩ => exact Alg.compat_symm (lawful_groundCodec (.base .string)) hl hs
    | ⟨1, _⟩, ⟨1, _⟩ => exact fun _ _ hp _ => hp

/-- `jsonClosed` meets its obligations: each stage after a lawful stage keeps its options
    compatible. -/
theorem Closed.obligations_json : jsonClosed.Obligations α :=
  ⟨trivial, fun _ hk i => match i with | ⟨0, _⟩ => obligations_jsonBody _ _ _ _ (hk 0)⟩

/-- **The host's recursive schema, as a closed codec, is lawful.** -/
theorem Closed.lawful_json : Lawful (jsonClosed.meaning α) :=
  Closed.sound Closed.typed_json Closed.obligations_json

/-- **`jsonClosed` is a fixed point**: it writes what its entry writes over `jsonClosed`. -/
theorem Closed.json_e_fix (v : Value) :
    (jsonClosed.meaning α).e v =
      (Alg.SFlat.interp (Alg.CStep (Alg.Scoped.TStep (Alg.tables dynSyn.o α dynTableA)) 0 Fin.elim0)
        jsonBody (fun _ => jsonClosed.meaning α) Fin.elim0).e v :=
  Closed.one_fix α jsonBody .host v

/-- `jsonClosed` writes a nested array through itself, and refuses an element it does not hold. -/
theorem Closed.json_vectors :
    (jsonClosed.meaning α).e (.arr [.str "a", .arr [.str "b"]]) = some (.l [.s "a", .l [.s "b"]])
    ∧ (jsonClosed.meaning α).e (.arr [.bool true]) = none
    ∧ (jsonClosed.meaning α).p (.l [.s "a", .l []]) = some (.arr [.str "a", .arr []]) :=
  ⟨rfl, rfl, rfl⟩

/-! ## The shapes that have no closed codec

Each shape is a flat graph. A scope term names an entry above every guard only below its own
position, and the inner term and the outer term of a `held` name no entry of their scope: the
type of a scope term holds no other leaf. `dagGuardB` decides the same refusal on a graph. -/

/-- **A graph has a form as a DAG of scopes**: a renaming of its entries is the graph form of a
    closed codec. -/
def Graph.DagForm (g : Graph) : Prop :=
  ∃ (π : Equiv.Perm (Fin g.N)) (d : Alg.Scoped.Closed dynSig g.N),
    ∀ m, d.graph m = (g.sys (π.symm m)).bind fun j => .leaf (π j)

/-- **The guard decides the form as a DAG of scopes** (`dagGuardB_iff_dsys`). -/
theorem Graph.dagForm_iff (g : Graph) : g.DagForm ↔ g.guarded = true :=
  Alg.dagGuardB_iff_dsys.symm

/-- The graph of `mu (var 0)`: one entry that names itself at its own input. -/
def unguardedGraph : Graph := ⟨1, fun _ => Scoped.Graph.Term.ref 0⟩

/-- The graph of `mu (union [var 0, string])`: an option names its own entry at its input. -/
def optionAtInputGraph : Graph :=
  ⟨1, fun _ => Scoped.Graph.Term.union [Scoped.Graph.Term.ref 0, Scoped.Graph.Term.string]⟩

/-- The graph of `mu (array (held false (var 0) opaque …))`: a `held` names its own entry. -/
def heldOnPathGraph : Graph :=
  ⟨1, fun _ => Scoped.Graph.Term.array
    (Scoped.Graph.Term.held false (Scoped.Graph.Term.ref 0) Scoped.Graph.Term.opaq (.caller 0, false) [])⟩

/-- **An entry that names itself at its own input has no closed codec**: its stages never grow. -/
theorem Graph.unguarded_no_dag : ¬ unguardedGraph.DagForm :=
  fun h => absurd ((Graph.dagForm_iff _).mp h) (by decide)

/-- **An option that names its own entry at its input has no closed codec.** -/
theorem Graph.option_at_input_no_dag : ¬ optionAtInputGraph.DagForm :=
  fun h => absurd ((Graph.dagForm_iff _).mp h) (by decide)

/-- **A `held` that names its own entry has no closed codec**, although a container guards the
    entry: the caller side of the `held` can make the input deeper. -/
theorem Graph.held_on_path_no_dag : ¬ heldOnPathGraph.DagForm :=
  fun h => absurd ((Graph.dagForm_iff _).mp h) (by decide)

/-- The graph of `jsonClosed`. -/
def jsonGraph : Graph :=
  ⟨1, fun _ => Scoped.Graph.Term.union
    [Scoped.Graph.Term.string, Scoped.Graph.Term.array (Scoped.Graph.Term.ref 0)]⟩

/-- The graph of `mu (array (mu (array (var 1))))`: two entries, each an array of the other. -/
def nestGraph : Graph := ⟨2, fun i => Scoped.Graph.Term.array (Scoped.Graph.Term.ref i.rev)⟩

/-- **An entry under a container has a closed codec**, and so do two entries that name each other
    under a container. -/
theorem Graph.container_path_dag : jsonGraph.DagForm ∧ nestGraph.DagForm :=
  ⟨(Graph.dagForm_iff _).mpr (by decide), (Graph.dagForm_iff _).mpr (by decide)⟩

end Calculus
