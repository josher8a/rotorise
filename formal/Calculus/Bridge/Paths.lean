import Calculus.Dynamo.Analysis.Path

/-!
# The readings of a path row

A path row states the decision of `at` on the host, and the frontier of the model at the path.
`pathReads` compares the two: the host gives a `HostAt`, and the model gives the frontier by
`Alg.Term.at`, or after a clause by `narrowFrames` and the frontier of the rest of the path. A
generated path module states each row through `pathRows` and `narrowRows`, and the kernel decides
the rows.

**What a row says.** Each `HostAt` form names a frontier, and the theorems below state the
frontier that `pathReads` accepts for each form. A refusal is no frontier. No codec is a frontier
whose frames each have the head `never`. Some options is a frontier with a `never` head and
with another head. Two declarations is a frontier with no `never` head, whose first frame
`frameSim` separates from another frame. One codec is a nonempty frontier whose frames each are
similar to the codec.

**Why a row compares shapes.** A frame holds a variable over its binder stack where the host holds
a thunk, and the host keeps one copy of each codec where the model keeps one frame per option. So
a row compares the shape of each frame, each binder entered and each variable read through its
binder.

**What similarity says.** `frameSim n f g` reads the heads of the two frames: `pathHead` enters
each binder and reads each variable through its binder, at most the length of the stack and two
more steps. The heads have one constructor, two primitives are equal by `groundEq`, two variables
past the stack name one outer binder, and the children are similar to one depth less. Similarity
to depth `n` is the law that the definition gives, and it is no law of meaning: `frameSim` reads
no predicate of a `refine` and no older reader of a `legacy`, so two frames similar at every
depth can have two meanings (`frameSim_reads_no_predicate`). A generated row reads the depth of
the resolved term and two more steps.
-/

namespace Calculus

/-- **Two primitives are one primitive**: the same base, or the same literal of one kind. -/
def groundEq : Ground → Ground → Bool
  | .base k, .base k' => decide (k = k')
  | .literal k v, .literal k' v' => if h : k = k' then decide (h ▸ v = v') else false
  | _, _ => false

/-- **The head of a frame**: a binder enters its body, and a variable reads the binder that it
    names. A variable that no binder binds is the head. -/
def pathHead : Nat → Alg.Frame dynSyn → Alg.Frame dynSyn
  | 0, f => f
  | n + 1, (.mu b, env) => pathHead n (b, .mu b :: env)
  | n + 1, (.var i, env) =>
      match env[i]? with
      | some m => pathHead n (m, env.drop (i + 1))
      | none => (.var i, env)
  | _ + 1, f => f

/-- **Two frames of one shape to depth `n`**, each binder entered and each variable read through
    its binder. A variable that no binder binds is compared past the stack. A predicate and an
    older reader are not read. -/
def frameSim (n : Nat) (f g : Alg.Frame dynSyn) : Bool :=
  match n with
  | 0 => true
  | n + 1 =>
    let x := pathHead (f.2.length + 2) f
    let y := pathHead (g.2.length + 2) g
    let sim := fun (s t : Term) => frameSim n (s, x.2) (t, y.2)
    let simL := fun (ss ts : List Term) =>
      ss.length == ts.length && (ss.zip ts).all fun p => sim p.1 p.2
    let simO := fun (s t : Option Term) => match s, t with
      | none, none => true
      | some s, some t => sim s t
      | _, _ => false
    let simS := fun (s t : ObjectSlot) => match s, t with
      | .req s, .req t | .optional s, .optional t | .fill s _, .fill t _ => sim s t
      | _, _ => false
    match x.1, y.1 with
    | .prim a, .prim b => groundEq a b
    | .opaq, .opaq | .never, .never => true
    | .var i, .var j => i - x.2.length == j - y.2.length
    | .set s, .set t => sim s t
    | .refine s _ _, .refine t _ _ | .legacy s _, .legacy t _ => sim s t
    | .held false s P k ks, .held false t Q l ls => sim s t && sim P Q && decide (k :: ks = l :: ls)
    | .list p sp sf, .list q tp tf => simL p q && simO sp tp && simL sf tf
    | .union os, .union ps => simL os ps
    | .object (.mk fs f w), .object (.mk gs g v) =>
        decide (∀ k : {k // k ∈ fs}, ∃ h : k.1 ∈ gs, simS (f k) (g ⟨k.1, h⟩) = true) &&
          fs.card == gs.card && simO w v
    | _, _ => false
termination_by structural n

/-- **A frame whose head is `never`**: an option that admits no value at the path. -/
def frameNever (f : Alg.Frame dynSyn) : Bool :=
  match (pathHead (f.2.length + 2) f).1 with
  | .never => true
  | _ => false

/-- **The decision of `at` at a path**, as the host states it. -/
inductive HostAt where
  /-- The walk refuses the path. -/
  | refused
  /-- No codec stands at the path. -/
  | vacant
  /-- Some options admit no value at the path, and some do. -/
  | someVariants
  /-- The options declare the path differently. -/
  | ambiguous
  /-- One codec stands at the path. -/
  | resolved (t : Term)

/-- **The frontier that a decision names.** A refusal is `none`. No codec is a frontier of `never`
    alone, the empty frontier included. Some options is a frontier with `never` and with another
    frame. Two declarations are a frontier with no `never` and two frames of two shapes. One codec
    is a frontier of frames of the shape of the codec. -/
def pathReads (n : Nat) : Option (List (Alg.Frame dynSyn)) → HostAt → Bool
  | none, .refused => true
  | some fs, .vacant => fs.all frameNever
  | some fs, .someVariants => fs.any frameNever && fs.any (!frameNever ·)
  | some (f :: fs), .ambiguous => !(f :: fs).any frameNever && fs.any (!frameSim n f ·)
  | some fs, .resolved t => !fs.isEmpty && fs.all (frameSim n · (t, []))
  | _, _ => false

/-- **The rows of the paths into a root**: `Alg.Term.at` at each path, read against the host. -/
def pathRows (n : Nat) (root : Term) (rows : List (List Alg.Seg × HostAt)) : Bool :=
  rows.all fun r => pathReads n (Alg.Term.at root r.1) r.2

/-- **The frames after a clause**: the options of the union that `narrow` keeps, each under the
    binder of a recursive union. -/
def narrowFrames (φ : Term) : Term → List (Alg.Frame dynSyn)
  | .union os => (Alg.narrow .dual φ os).map ((·, []))
  | .mu (.union os) => (Alg.narrow .dual φ os).map ((·, [.mu (.union os)]))
  | t => [(t, [])]

/-- **The rows of the clauses at a union**: for each clause, `narrow`, then the frontier of the
    rest of each path. -/
def narrowRows (n : Nat) (u : Term) (rows : List (Term × List (List Alg.Seg × HostAt))) : Bool :=
  rows.all fun c => let fs := narrowFrames c.1 u
    c.2.all fun r => pathReads n (Alg.atG Alg.Frame.child r.1 fs) r.2

/-! ## The frontier that each decision names -/

/-- **A frame reads `never` exactly where its head is `never`.** -/
theorem frameNever_iff (f : Alg.Frame dynSyn) :
    frameNever f = true ↔ (pathHead (f.2.length + 2) f).1 = .never := by
  unfold frameNever
  split <;> simp_all

/-- **A refusal is no frontier.** -/
theorem pathReads_refused (n : Nat) (r : Option (List (Alg.Frame dynSyn))) :
    pathReads n r .refused = true ↔ r = none := by
  rcases r with _ | fs <;> simp [pathReads]

/-- **No codec is a frontier of `never` heads**, the empty frontier included. -/
theorem pathReads_vacant (n : Nat) (r : Option (List (Alg.Frame dynSyn))) :
    pathReads n r .vacant = true ↔ ∃ fs, r = some fs ∧ ∀ f ∈ fs, frameNever f = true := by
  rcases r with _ | fs <;> simp [pathReads]

/-- **Some options is a frontier with a `never` head and with another head.** -/
theorem pathReads_someVariants (n : Nat) (r : Option (List (Alg.Frame dynSyn))) :
    pathReads n r .someVariants = true ↔ ∃ fs, r = some fs ∧
      (∃ f ∈ fs, frameNever f = true) ∧ ∃ f ∈ fs, frameNever f = false := by
  rcases r with _ | fs <;> simp [pathReads]

/-- **Two declarations are a frontier with no `never` head**, whose first frame is not similar
    to another frame. -/
theorem pathReads_ambiguous (n : Nat) (r : Option (List (Alg.Frame dynSyn))) :
    pathReads n r .ambiguous = true ↔ ∃ f fs, r = some (f :: fs) ∧
      (∀ g ∈ f :: fs, frameNever g = false) ∧ ∃ g ∈ fs, frameSim n f g = false := by
  rcases r with _ | _ | ⟨f, fs⟩ <;> simp [pathReads]

/-- **One codec is a nonempty frontier**, whose frames each are similar to the codec. -/
theorem pathReads_resolved (n : Nat) (r : Option (List (Alg.Frame dynSyn))) (t : Term) :
    pathReads n r (.resolved t) = true ↔ ∃ fs, r = some fs ∧ fs ≠ [] ∧
      ∀ f ∈ fs, frameSim n f (t, []) = true := by
  rcases r with _ | fs <;> simp [pathReads]

/-! ## Similarity is no law of meaning -/

/-- **Two refinements are similar where their inner terms are**, whatever their predicates. -/
theorem frameSim_refine (n : Nat) (s t : Term) (p q : Pred) (pA qA : dynSyn.PredA)
    (env env' : List Term) :
    frameSim (n + 1) (.refine s p pA, env) (.refine t q qA, env') =
      frameSim n (s, env) (t, env') := by
  rfl

/-- **Similarity at every depth does not give one meaning.** Two refinements of `string` by two
    predicates are similar at every depth, and the one admits a string that the other refuses. -/
theorem frameSim_reads_no_predicate (α : Table) (β : Alg.Table dynSyn.op) :
    ∃ f g : Alg.Frame dynSyn, (∀ n, frameSim n f g = true) ∧
      (Alg.Frame.sem α β f).T (.str "") ∧ ¬ (Alg.Frame.sem α β g).T (.str "") := by
  refine ⟨(.refine Term.string (.closure fun _ => true) (), []),
    (.refine Term.string (.closure fun _ => false) (), []), ?_, ?_, ?_⟩
  · intro n
    rcases n with _ | n
    · rfl
    · rw [frameSim_refine]
      rcases n with _ | n <;> rfl
  · exact ⟨rfl, rfl⟩
  · exact fun h => Bool.false_ne_true h.2

end Calculus
