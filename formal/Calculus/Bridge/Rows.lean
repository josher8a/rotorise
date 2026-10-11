import Calculus.Bridge.Vectors
import Calculus.Dynamo.Analysis.Compat
import Calculus.Dynamo.Analysis.Disjoint
import Calculus.Dynamo.Analysis.ExactA
import Calculus.Dynamo.Lang.Store
import Calculus.Dynamo.Lang.Scope

/-!
# Verdicts, from a checked row list

A generated vector file states many verdicts of one form as a list of rows. A row is the name of
its vector, then the data of the vector. The comparator of a form answers one row. The file states
the comparator of each list in two projections: the kernel decides `failing ok rows = []`, and an
`#eval` prints `failing ok rows` at one instance of the caller functions. So the diagnostic names a
failing row by the comparator that the kernel reads.

The law of each comparator makes `true` the statement of the row. The lemmas of the separation
forms lift a checked list to the verdict of each row. The verdict of a separation row is the full
separation verdict of one pair. The guard reads the rooted terms, and compatibility reads the open
terms.
-/

namespace Calculus

/-- The names of the rows whose comparator answers `false`. -/
def failing {α : Type} (ok : α → Bool) (rows : List (String × α)) : List String :=
  (rows.filter fun p => !ok p.2).map Prod.fst

/-- **A list with no failing row holds the comparator at each row.** -/
theorem ok_of_failing {α : Type} {ok : α → Bool} {rows : List (String × α)}
    (h : failing ok rows = []) : ∀ p ∈ rows, ok p.2 = true := fun p hp =>
  Bool.eq_false_imp_eq_true.mp fun hq => absurd
    ((congrArg (p.1 ∈ ·) h).mp
      (List.mem_map_of_mem (List.mem_filter.mpr ⟨hp, by rw [hq]; rfl⟩)))
    List.not_mem_nil

/-! ## The evaluation forms -/

/-- A row of a write: the model writes the attribute that `src/` wrote. -/
def writesOk (p : Nat × Closed × Value × Attr) : Bool :=
  check p.1 ((p.2.1.meaning (libTable noCallers)).e p.2.2.1) (some p.2.2.2) == Verdict.same

/-- The law of `writesOk`: the `check` of the written attribute answers `.same`. -/
theorem writesOk_iff (p : Nat × Closed × Value × Attr) : writesOk p = true ↔
    check p.1 ((p.2.1.meaning (libTable noCallers)).e p.2.2.1) (some p.2.2.2) = .same :=
  beq_iff_eq

/-- A row of a refused value: the model writes nothing, as `src/` refused the value. -/
def writesNothingOk (p : Closed × Value) : Bool :=
  ((p.1.meaning (libTable noCallers)).e p.2).isNone

/-- The law of `writesNothingOk`: the model's write is `none`. -/
theorem writesNothingOk_iff (p : Closed × Value) :
    writesNothingOk p = true ↔ (p.1.meaning (libTable noCallers)).e p.2 = none :=
  Option.isNone_iff_eq_none

/-- A row of a read: the model reads the value that `src/` read. -/
def readsOk (p : Nat × Closed × Attr × Value) : Bool :=
  vcheck p.1 ((p.2.1.meaning (libTable noCallers)).p p.2.2.1) (some p.2.2.2) == Verdict.same

/-- The law of `readsOk`: the `vcheck` of the read value answers `.same`. -/
theorem readsOk_iff (p : Nat × Closed × Attr × Value) : readsOk p = true ↔
    vcheck p.1 ((p.2.1.meaning (libTable noCallers)).p p.2.2.1) (some p.2.2.2) = .same :=
  beq_iff_eq

/-- A row of a refused attribute: the model reads nothing, as `src/` refused the attribute. -/
def readsNothingOk (p : Closed × Attr) : Bool :=
  ((p.1.meaning (libTable noCallers)).p p.2).isNone

/-- The law of `readsNothingOk`: the model's read is `none`. -/
theorem readsNothingOk_iff (p : Closed × Attr) :
    readsNothingOk p = true ↔ (p.1.meaning (libTable noCallers)).p p.2 = none :=
  Option.isNone_iff_eq_none

/-- A row of a guard: the guard of a DAG of scopes on the graph gives the answer of `src/`. -/
def guardsOk (p : Graph × Bool) : Bool := p.1.guarded == p.2

/-- The law of `guardsOk`: the guard equals the answer. -/
theorem guardsOk_iff (p : Graph × Bool) : guardsOk p = true ↔ p.1.guarded = p.2 :=
  beq_iff_eq

/-- A row of an admission: the read row of the closed codec gives the answer of the decoder of
    `src/`. -/
def admitsOk (p : Closed × Attr × Bool) : Bool := p.1.AdmA (libTable noCallers) p.2.1 == p.2.2

/-- The law of `admitsOk`: the read row equals the answer. -/
theorem admitsOk_iff (p : Closed × Attr × Bool) :
    admitsOk p = true ↔ p.1.AdmA (libTable noCallers) p.2.1 = p.2.2 :=
  beq_iff_eq

/-! ## Disjointness -/

/-- A disjointness row: the two terms, then the answers of `src/`'s `disjoint` and `viewsDisjoint`. -/
def disjointOk (p : Term × Term × Bool × Bool) : Bool :=
  (Alg.Term.disjoint pair0 p.1 p.2.1 == p.2.2.1) && (viewsDisjoint p.1 p.2.1 == p.2.2.2)

/-- The law of `disjointOk`: both answers of the model equal the answers of `src/`. -/
theorem disjointOk_iff (p : Term × Term × Bool × Bool) : disjointOk p = true ↔
    Alg.Term.disjoint pair0 p.1 p.2.1 = p.2.2.1 ∧ viewsDisjoint p.1 p.2.1 = p.2.2.2 := by
  rw [disjointOk, Bool.and_eq_true, beq_iff_eq, beq_iff_eq]

/-! ## Separations -/

/-- An accepted pair: the guard accepts both rooted terms, and the decision accepts the open pair. -/
def acceptedOk (p : Term × Term × Term × Term) : Bool :=
  Alg.Term.guarded p.1 && Alg.Term.guarded p.2.1 && Alg.compatPair dynOracle p.2.2.1 p.2.2.2

/-- A pair refused at compatibility: the guard accepts both rooted terms, and the decision refuses
    the open pair. -/
def refusedOk (p : Term × Term × Term × Term) : Bool :=
  Alg.Term.guarded p.1 && Alg.Term.guarded p.2.1 && !Alg.compatPair dynOracle p.2.2.1 p.2.2.2

/-- A pair refused at the guard: the guard refuses a rooted term. -/
def guardRefusedOk (p : Term × Term) : Bool := !(Alg.Term.guarded p.1 && Alg.Term.guarded p.2)

/-- The guard column of a pair: the guard on the two rooted terms gives the answer of `src/`. -/
def pairGuardOk (p : Term × Term × Bool) : Bool :=
  (Alg.Term.guarded p.1 && Alg.Term.guarded p.2.1) == p.2.2

/-- The law of `pairGuardOk`: the guard on the pair equals the answer. -/
theorem pairGuardOk_iff (p : Term × Term × Bool) :
    pairGuardOk p = true ↔ (Alg.Term.guarded p.1 && Alg.Term.guarded p.2.1) = p.2.2 :=
  beq_iff_eq

/-- **An accepted pair, at each row.** The guard accepts both options, and the decision
    discharges the union's obligation at every caller table. -/
theorem accepted_of_rows {rows : List (String × Term × Term × Term × Term)}
    (h : failing acceptedOk rows = []) (κ : Callers) : ∀ p ∈ rows,
    (Alg.Term.guarded p.2.1 && Alg.Term.guarded p.2.2.1) = true ∧
    ((∀ t ∈ [p.2.2.2.1, p.2.2.2.2], Lawful (denote (libTable κ) t)) →
      PairwiseCompat (libTable κ) [p.2.2.2.1, p.2.2.2.2]) := by
  intro p hp
  have h := ok_of_failing h p hp
  rw [acceptedOk, Bool.and_eq_true] at h
  exact ⟨h.1, fun hl => pairwiseCompat_of_compatPair h.2 hl⟩

/-- **A pair refused at compatibility, at each row.** The guard accepts both options, and the
    decision refuses the pair. -/
theorem refused_of_rows {rows : List (String × Term × Term × Term × Term)}
    (h : failing refusedOk rows = []) : ∀ p ∈ rows,
    (Alg.Term.guarded p.2.1 && Alg.Term.guarded p.2.2.1) = true ∧
    Alg.compatPair dynOracle p.2.2.2.1 p.2.2.2.2 = false := by
  intro p hp
  have h := ok_of_failing h p hp
  rw [refusedOk, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h

/-- **A pair refused at the guard, at each row.** The guard refuses an option. -/
theorem guardRefused_of_rows {rows : List (String × Term × Term)}
    (h : failing guardRefusedOk rows = []) :
    ∀ p ∈ rows, (Alg.Term.guarded p.2.1 && Alg.Term.guarded p.2.2) = false := by
  intro p hp
  have h := ok_of_failing h p hp
  rwa [guardRefusedOk, Bool.not_eq_true'] at h

end Calculus
