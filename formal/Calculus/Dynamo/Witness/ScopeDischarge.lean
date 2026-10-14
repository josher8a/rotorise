import Calculus.Dynamo.Lang.ScopeSound

/-!
# A recursive schema, as a closed codec

The host's recursive schema for JSON as a closed codec (`jsonClosed`), carried through
`Closed.sound`, and the shapes that have no closed codec.

A stratified system names an entry above every guard only below its own position, and below a
wall it names no entry: the type of a stratified term holds no other leaf. The graph form of a
stratified system passes `graphGuard` under each renaming of its entries
(`Graph.guarded_of_stratForm`). So a shape that `graphGuard` refuses has no stratified system with
that graph as its graph form.
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

/-! ## The shapes that have no stratified form

Each shape is a flat graph. A stratified term names an entry above every guard only below its own
position, and below a wall it names no entry: the type of a stratified term holds no other leaf. A
graph that `graphGuard` refuses has no stratified form. -/

/-- **A graph has a stratified form**: a renaming of its entries is the graph form of a stratified
    system. -/
def Graph.StratForm (g : Graph) : Prop :=
  ∃ (π : Equiv.Perm (Fin g.N)) (s : Alg.SSys (Alg.Scoped.TSig dynSig) g.N),
    ∀ m, s.graph m = (g.sys (π.symm m)).bind fun j => .leaf (π j)

/-- **A graph that has a stratified form passes the guard**: the graph form of the stratified system
    passes `graphGuard`, and the renaming keeps the guard back to the graph. -/
theorem Graph.guarded_of_stratForm (g : Graph) (h : g.StratForm) : g.guarded = true := by
  obtain ⟨π, s, hs⟩ := h
  exact Alg.graphGuard_of_rename π hs (Alg.SSys.graphGuard s)

/-- The graph of one entry whose body is `ref 0`: the entry names itself at its own input. -/
def unguardedGraph : Graph := ⟨1, fun _ => Scoped.Graph.Term.ref 0⟩

/-- The graph of one entry whose body is `union [ref 0, string]`: an option names its own entry at
    its input. -/
def optionAtInputGraph : Graph :=
  ⟨1, fun _ => Scoped.Graph.Term.union [Scoped.Graph.Term.ref 0, Scoped.Graph.Term.string]⟩

/-- The graph of one entry whose body is `array (held false (ref 0) opaque …)`: a `held` names its
    own entry. -/
def heldOnPathGraph : Graph :=
  ⟨1, fun _ => Scoped.Graph.Term.array
    (Scoped.Graph.Term.held false (Scoped.Graph.Term.ref 0) Scoped.Graph.Term.opaq (.caller 0, false) [])⟩

/-- **An entry that names itself at its own input has no stratified form**: its stages never
    grow. -/
theorem Graph.unguarded_no_strat : ¬ unguardedGraph.StratForm :=
  fun h => absurd (Graph.guarded_of_stratForm _ h) (by decide)

/-- **An option that names its own entry at its input has no stratified form.** -/
theorem Graph.option_at_input_no_strat : ¬ optionAtInputGraph.StratForm :=
  fun h => absurd (Graph.guarded_of_stratForm _ h) (by decide)

/-- **A `held` that names its own entry has no stratified form**, although a container guards the
    entry: the caller side of the `held` can make the input deeper. -/
theorem Graph.held_on_path_no_strat : ¬ heldOnPathGraph.StratForm :=
  fun h => absurd (Graph.guarded_of_stratForm _ h) (by decide)

/-- The graph of `jsonClosed`. -/
def jsonGraph : Graph :=
  ⟨1, fun _ => Scoped.Graph.Term.union
    [Scoped.Graph.Term.string, Scoped.Graph.Term.array (Scoped.Graph.Term.ref 0)]⟩

/-- The graph of two entries whose bodies are `array (ref 1)` and `array (ref 0)`: each entry is an
    array of the other. -/
def nestGraph : Graph := ⟨2, fun i => Scoped.Graph.Term.array (Scoped.Graph.Term.ref i.rev)⟩

/-- The stratified system of one entry: a string, or an array of the entry. -/
def jsonStrat : Alg.SSys (Alg.Scoped.TSig dynSig) 1 := fun _ =>
  .node (Alg.Scoped.TOp.union 2)
    (Fin.cases (.node (Alg.Scoped.TOp.prim (Ground.base .string)) fun p => nomatch p)
      fun _ => .node (Alg.Scoped.TOp.list 0 1 0) fun _ => .leaf (0 : Fin 1))

/-- **An entry under a container has a stratified form**: the graph form of `jsonStrat` is
    `jsonGraph`. -/
theorem Graph.json_strat : jsonGraph.StratForm := by
  refine ⟨Equiv.refl _, jsonStrat, fun m => ?_⟩
  match m with
  | ⟨0, _⟩ =>
    refine congrArg (Alg.Flat.node _) (funext fun p => ?_)
    match p with
    | ⟨0, _⟩ => exact congrArg (Alg.Flat.node _) (funext fun p => nomatch p)
    | ⟨1, _⟩ =>
      refine congrArg (Alg.Flat.node _) (funext fun p => ?_)
      match p with
      | .inl p => exact p.elim0
      | .inr (.inl _) => rfl
      | .inr (.inr p) => exact p.elim0

/-- The stratified system of two entries, each an array of the other. -/
def nestStrat : Alg.SSys (Alg.Scoped.TSig dynSig) 2 := fun i =>
  .node (Alg.Scoped.TOp.list 0 1 0) fun _ => .leaf (i.rev : Fin 2)

/-- **Two entries that name each other under a container have a stratified form**: the graph form
    of `nestStrat` is `nestGraph`. -/
theorem Graph.nest_strat : nestGraph.StratForm := by
  refine ⟨Equiv.refl _, nestStrat, fun m => ?_⟩
  match m with
  | ⟨0, _⟩ | ⟨1, _⟩ =>
    refine congrArg (Alg.Flat.node _) (funext fun p => ?_)
    match p with
    | .inl p => exact p.elim0
    | .inr (.inl _) => rfl
    | .inr (.inr p) => exact p.elim0

/-- **An entry under a container passes the guard**, and so do two entries that name each other
    under a container: each has a stratified form. -/
theorem Graph.container_path_guarded : jsonGraph.guarded = true ∧ nestGraph.guarded = true :=
  ⟨Graph.guarded_of_stratForm _ Graph.json_strat, Graph.guarded_of_stratForm _ Graph.nest_strat⟩

end Calculus
