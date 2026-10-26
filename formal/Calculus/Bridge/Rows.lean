import Calculus.Bridge.Vectors
import Calculus.Dynamo.Analysis.ScopeCompat
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
separation verdict of one pair. A row of a pair that the guard accepts holds two closed codecs: a
closed codec exists only for a guarded codec, so the type of the row states the guard, and the row
states the compatibility decision. A row of a pair that the guard refuses holds two graphs. A row
of a meet holds two closed codecs, the closed codec of the meet that `src/` built, and one pair of a
value and an attribute: the meet holds the pair where both factors hold the pair. The row reads each
factor as written, so the row states the cover and not the equation, because `src/` reads each
factor open.
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

/-- A row of a guard: the graph guard on the graph gives the answer of `src/`. -/
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

/-- A disjointness row: the two closed codecs, then the answers of `src/`'s `disjoint` and
    `viewsDisjoint`. The model reads the decision over the graphs, `Closed.disjoint` and
    `Closed.viewsDisjoint`, so a row that states `true` states a pair that shares no datum
    (`Closed.disjoint_sound`, `Closed.viewsDisjoint_sound`). -/
def disjointOk (p : Closed × Closed × Bool × Bool) : Bool :=
  (p.1.disjoint p.2.1 == p.2.2.1) && (p.1.viewsDisjoint p.2.1 == p.2.2.2)

/-- The law of `disjointOk`: both answers of the model equal the answers of `src/`. -/
theorem disjointOk_iff (p : Closed × Closed × Bool × Bool) : disjointOk p = true ↔
    p.1.disjoint p.2.1 = p.2.2.1 ∧ p.1.viewsDisjoint p.2.1 = p.2.2.2 := by
  rw [disjointOk, Bool.and_eq_true, beq_iff_eq, beq_iff_eq]

/-! ## Separations -/

/-- An accepted pair: the decision accepts the two closed codecs. -/
def acceptedOk (p : Closed × Closed) : Bool := p.1.compatPair p.2

/-- An accepted pair of one option twice: the decision over one scope accepts the closed codec. -/
def acceptedOneOk (p : Closed) : Bool := p.compatOne

/-- A pair refused at compatibility: the decision refuses the two closed codecs. -/
def refusedOk (p : Closed × Closed) : Bool := !p.1.compatPair p.2

/-- A pair refused at the guard: the graph guard refuses a graph. -/
def guardRefusedOk (p : Graph × Graph) : Bool := !(p.1.guarded && p.2.guarded)

/-- The guard column of a pair: the guard on the two graphs gives the answer of `src/`. -/
def pairGuardOk (p : Graph × Graph × Bool) : Bool :=
  (p.1.guarded && p.2.1.guarded) == p.2.2

/-- The law of `pairGuardOk`: the guard on the pair equals the answer. -/
theorem pairGuardOk_iff (p : Graph × Graph × Bool) :
    pairGuardOk p = true ↔ (p.1.guarded && p.2.1.guarded) = p.2.2 :=
  beq_iff_eq

/-- **An accepted pair, at each row.** At every caller table, the two meanings of two lawful
    options are `Compat` in each order, which is the obligation of the union. -/
theorem accepted_of_rows {rows : List (String × Closed × Closed)}
    (h : failing acceptedOk rows = []) (κ : Callers) : ∀ p ∈ rows,
    Lawful (p.2.1.meaning (libTable κ)) → Lawful (p.2.2.meaning (libTable κ)) →
      Alg.Compat (p.2.1.meaning (libTable κ)) (p.2.2.meaning (libTable κ)) ∧
        Alg.Compat (p.2.2.meaning (libTable κ)) (p.2.1.meaning (libTable κ)) :=
  fun p hp => Closed.compat_of_compatPair (ok_of_failing h p hp) (libTable κ)

/-- **An accepted pair of one option twice, at each row.** At every caller table, the meaning of
    a lawful option is `Compat` with itself, which is the obligation of the union. -/
theorem acceptedOne_of_rows {rows : List (String × Closed)}
    (h : failing acceptedOneOk rows = []) (κ : Callers) : ∀ p ∈ rows,
    Lawful (p.2.meaning (libTable κ)) → Alg.Compat (p.2.meaning (libTable κ)) (p.2.meaning (libTable κ)) :=
  fun p hp => Closed.compat_of_compatOne (ok_of_failing h p hp) (libTable κ)

/-- **A pair refused at compatibility, at each row.** The decision refuses the pair. -/
theorem refused_of_rows {rows : List (String × Closed × Closed)}
    (h : failing refusedOk rows = []) : ∀ p ∈ rows, p.2.1.compatPair p.2.2 = false := by
  intro p hp
  have h := ok_of_failing h p hp
  rwa [refusedOk, Bool.not_eq_true'] at h

/-- **A pair refused at the guard, at each row.** The guard refuses a graph. -/
theorem guardRefused_of_rows {rows : List (String × Graph × Graph)}
    (h : failing guardRefusedOk rows = []) :
    ∀ p ∈ rows, (p.2.1.guarded && p.2.2.guarded) = false := by
  intro p hp
  have h := ok_of_failing h p hp
  rwa [guardRefusedOk, Bool.not_eq_true'] at h

/-! ## Meets -/

/-- **The cover at three verdicts**: each verdict settles, and the third is `.same` where the first
    two are `.same`. A run out of fuel fails the cover. -/
def covers : Verdict → Verdict → Verdict → Bool
  | .exhausted, _, _ | _, .exhausted, _ | _, _, .exhausted => false
  | .same, .same, m => m == .same
  | _, _, _ => true

/-- Where the cover holds and neither of the first two verdicts is `.differ`, the third is `.same`. -/
theorem covers_same {a b m : Verdict} (h : covers a b m = true) (ha : a ≠ .differ)
    (hb : b ≠ .differ) : m = .same := by
  cases a <;> cases b <;> cases m <;> simp_all [covers]

/-- A row of a meet: `src/`'s meet `M` of `A` and `B` writes the attribute `s` from the value `v`
    wherever the model's `A` and `B` both write `s` from `v`. -/
def meetCoversOk : Nat × Closed × Closed × Closed × Value × Attr → Bool
  | (n, A, B, M, v, s) =>
    let mem := fun t : Closed => check n ((t.meaning (libTable noCallers)).e v) (some s)
    covers (mem A) (mem B) (mem M)

/-- The law of `meetCoversOk`: where the model's `A` and `B` write `s` from `v`, the model's `M`
    writes `s` from `v`. -/
theorem meetCoversOk_sound {n : Nat} {A B M : Closed} {v : Value} {s : Attr}
    (h : meetCoversOk (n, A, B, M, v, s) = true)
    (hA : (A.meaning (libTable noCallers)).e v = some s)
    (hB : (B.meaning (libTable noCallers)).e v = some s) :
    (M.meaning (libTable noCallers)).e v = some s :=
  check_same (covers_same h (fun hd => check_differ hd hA) (fun hd => check_differ hd hB))

/-- **A meet row covers the meet of the two meanings, at each row.** A pair of `Codec.meet` of the
    meanings of `A` and `B` at the write is a pair of the meaning of `M`. The decision of equality
    at `Attr` is a parameter: `Codec.meet` reads one, and the checker reads none. -/
theorem meetCovers_of_rows [DecidableEq Attr]
    {rows : List (String × Nat × Closed × Closed × Closed × Value × Attr)}
    (h : failing meetCoversOk rows = []) :
    ∀ x n A B M v s, (x, n, A, B, M, v, s) ∈ rows →
      (Alg.Codec.meet (A.meaning (libTable noCallers)) (B.meaning (libTable noCallers))).e v =
        some s → (M.meaning (libTable noCallers)).e v = some s :=
  fun _ _ _ _ _ _ _ hp hm =>
    let ⟨hA, hB⟩ := Alg.Codec.meet_f.mp hm
    meetCoversOk_sound (ok_of_failing h _ hp) hA hB

end Calculus
