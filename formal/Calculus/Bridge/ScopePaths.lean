import Calculus.Bridge.Paths
import Calculus.Bridge.Vectors
import Calculus.Dynamo.Analysis.ScopePath

/-!
# The readings of a path row over a closed codec

A path row over a closed codec states the decision of `at` on the host, and the frontier of the
graph at the path. `pathReadC` compares the two: the host gives a `HostAtC`, and the graph gives
the frontier by `Rooted.at`, or after a clause by `narrowC` and the frontier of the rest of the
path. `PathRowsC` and `NarrowRowsC` state the rows, beside today's `PathRows` and `NarrowRows`.

**What a row says** is what today's row says, over graph frames. A refusal is no frontier. No
codec is a frontier whose frames each have the head `never`. Some options is a frontier with a
`never` head and another head. One codec is a frontier with no `never` head whose frames are one
frame, and two declarations hold two frames.

**What `frameSameC` reads.** Two frames are one frame where their closed codecs have one count of
entries and one datum at each position of each entry, and their terms have one datum at each
position. An entry is one datum with itself, so two paths to one entry give one frame. A function
and a fill value are not read, as in `frameSame`: two refinements by two closures are one frame
(`pathKindC_reads_no_closure`). Equal frames have one meaning (`pathReadC_resolved_sem`), so a
resolved row certifies the meaning of the host's decision.
-/

namespace Calculus

open Alg (Seg)
open Alg.Scoped (GFrame Rooted narrowC)

/-- **Two operations of one datum**: one constructor, one primitive, one data predicate, one
    adapter word, one set of names with slots of one presence, and one arity. A closure, a reader
    and a fill value are not read. -/
def opSame : Alg.Scoped.TOp dynSig → Alg.Scoped.TOp dynSig → Bool
  | .prim a, .prim b => groundEq a b
  | .opaq, .opaq | .never, .never | .set, .set => true
  | .list a s b, .list a' s' b' => decide (a = a') && decide (s = s') && decide (b = b')
  | .refine p _, .refine q _ => predSame p q
  | .held false k ks, .held false l ls => decide (k :: ks = l :: ls)
  | .legacy _, .legacy _ => true
  | .obj fs md w, .obj gs md' w' =>
      decide (∀ k : {k // k ∈ fs}, ∃ h : k.1 ∈ gs, slotSame (md k) (md' ⟨k.1, h⟩) = true) &&
        decide (∀ k : {k // k ∈ gs}, k.1 ∈ fs) && decide (w = w')
  | .union m, .union m' => decide (m = m')
  | _, _ => false
where
  /-- Two slot presences of one datum. A fill value is not read. -/
  slotSame : Alg.Scoped.SlotMode dynSig → Alg.Scoped.SlotMode dynSig → Bool
    | .req, .req | .opt, .opt | .fill _, .fill _ => true
    | _, _ => false

/-- **Two graph terms of one datum**: one entry, or one operation with children of one datum,
    position by position. -/
def sameDataC {N N' : Nat} : Alg.Scoped.Graph dynSig N → Alg.Scoped.Graph dynSig N' → Bool
  | .leaf i, .leaf j => decide (i.val = j.val)
  | .node o a, .node o' a' =>
      opSame o o' && decide ((Alg.Scoped.TOp.pos o).length = (Alg.Scoped.TOp.pos o').length) &&
        ((Alg.Scoped.TOp.pos o).zip ((Alg.Scoped.TOp.pos o').map a')).all fun q =>
          sameDataC (a q.1) q.2
  | _, _ => false

/-- **Two frames that are one frame**: closed codecs of one datum at each entry, and terms of one
    datum. -/
def frameSameC (f g : GFrame dynSig) : Bool :=
  decide (f.N = g.N) && ((List.ofFn f.d.graph).zip (List.ofFn g.d.graph)).all
    (fun q => sameDataC q.1 q.2) && sameDataC f.t g.t

/-- **The head of a frame**: an entry reads its body. -/
def pathHeadC (f : GFrame dynSig) : Nat → Alg.Scoped.Graph dynSig f.N → Alg.Scoped.Graph dynSig f.N
  | 0, t => t
  | n + 1, .leaf j => pathHeadC f n (f.d.graph j)
  | _ + 1, t => t

/-- **A frame whose head is `never`**: an option that admits no value at the path. -/
def frameNeverC (f : GFrame dynSig) : Bool :=
  match pathHeadC f (f.N + 2) f.t with
  | .node .never _ => true
  | _ => false

/-- **The decision of `at` at a path, over a closed codec**, as the host states it. -/
inductive HostAtC where
  /-- The walk refuses the path. -/
  | refused
  /-- No codec stands at the path. -/
  | vacant
  /-- Some options admit no value at the path, and some do. -/
  | someVariants
  /-- The options declare the path differently. -/
  | ambiguous
  /-- One codec stands at the path: the frontier. -/
  | resolved (f : GFrame dynSig) (fs : List (GFrame dynSig))

/-- The decision that the host states. -/
def HostAtC.kind : HostAtC → PathKind
  | .refused => .refused
  | .vacant => .vacant
  | .someVariants => .someVariants
  | .ambiguous => .ambiguous
  | .resolved _ _ => .resolved

/-- **The decision that a frontier of graph frames names.** -/
def pathKindC : Option (List (GFrame dynSig)) → PathKind
  | none => .refused
  | some [] => .vacant
  | some (f :: gs) =>
      kindOf ((f :: gs).any frameNeverC) ((f :: gs).all frameNeverC) (gs.all (frameSameC f))

/-- **What a row reads**: the decision of the frontier, and the frontier where one codec stands. -/
def pathReadC (r : Option (List (GFrame dynSig))) :
    HostAtC → Bool × Option (List (GFrame dynSig))
  | .resolved _ _ => (decide (pathKindC r = .resolved), r)
  | h => (decide (pathKindC r = h.kind), none)

/-- **What the host states that a row reads.** -/
def HostAtC.claim : HostAtC → Bool × Option (List (GFrame dynSig))
  | .resolved f fs => (true, some (f :: fs))
  | _ => (true, none)

/-- **The rows of the paths into a closed codec**: `Rooted.at` at each path reads what the host
    states. -/
abbrev PathRowsC (root : Closed) (rows : List (List Seg × HostAtC)) : Prop :=
  rows.map (fun r => pathReadC (Alg.Scoped.Rooted.at (S := dynSyn) root.rooted r.1) r.2) =
    rows.map (·.2.claim)

/-- **The rows of the clauses at a union of closed options**: for each clause, `narrowC`, then the
    frontier of the rest of each path reads what the host states. -/
abbrev NarrowRowsC (os : List Closed) (rows : List (Closed × List (List Seg × HostAtC))) : Prop :=
  rows.map (fun c => c.2.map fun r =>
      pathReadC (Alg.atG (GFrame.child (S := dynSyn)) r.1
        ((narrowC (S := dynSyn) .dual c.1.rooted (os.map Closed.rooted)).map Rooted.frame)) r.2) =
    rows.map (·.2.map (·.2.claim))

/-- **One codec is its frontier**: the frames of the graph are one frame, and they are the
    recorded frames, one for one. -/
theorem pathReadC_resolved (r : Option (List (GFrame dynSig))) (f : GFrame dynSig)
    (fs : List (GFrame dynSig)) :
    pathReadC r (.resolved f fs) = (HostAtC.resolved f fs).claim ↔
      pathKindC r = .resolved ∧ r = some (f :: fs) :=
  ⟨fun he => ⟨of_decide_eq_true (congrArg Prod.fst he), congrArg Prod.snd he⟩,
    fun ⟨hk, hr⟩ => by rw [pathReadC, decide_eq_true hk, hr]; rfl⟩

/-- **A resolved row certifies meaning**: each frame of the frontier denotes what the recorded
    frame denotes, at every table. -/
theorem pathReadC_resolved_sem {r : Option (List (GFrame dynSig))} {f : GFrame dynSig}
    {fs : List (GFrame dynSig)} (h : pathReadC r (.resolved f fs) = (HostAtC.resolved f fs).claim)
    (τ : (s : Bool) → Alg.TableAt dynSig s) :
    (r.getD []).map (GFrame.sem (S := dynSyn) τ) = (f :: fs).map (GFrame.sem (S := dynSyn) τ) := by
  rw [((pathReadC_resolved r f fs).mp h).2]; rfl

/-- A refinement of `string` by a closure, as a frame of no entry. -/
private def refineFrame (q : Attr → Bool) : GFrame dynSig :=
  ⟨0, .nil, .node (.refine (.closure q) ()) fun _ => .node (.prim (.base .string)) Empty.elim⟩

/-- **No closure is read**: two refinements of `string` by two closures are one codec to the
    decision, and the one admits a string that the other refuses. -/
theorem pathKindC_reads_no_closure (α : Table) :
    ∃ f g : GFrame dynSig, pathKindC (some [f, g]) = .resolved ∧
      (GFrame.sem (S := dynSyn) (Alg.tables dynSyn.o α dynTableA) f).T (.str "") ∧
      ¬ (GFrame.sem (S := dynSyn) (Alg.tables dynSyn.o α dynTableA) g).T (.str "") := by
  refine ⟨refineFrame fun _ => true, refineFrame fun _ => false, rfl, ?_, ?_⟩
  · exact ⟨rfl, rfl⟩
  · exact fun h => Bool.false_ne_true h.2

/-! ## Vectors -/

private abbrev one (t : Scoped.Term 0 1 0) : Closed :=
  ⟨1, .snoc (c := 0) (n := 1) .nil (fun i => match i with | ⟨0, _⟩ => t), 0⟩

private abbrev itemM : Closed := one (Scoped.Term.object (Scoped.Body.mk {"m"} (fun _ =>
  Scoped.ObjectSlot.req (Scoped.Term.union [
    Scoped.Term.object (Scoped.Body.mk {"tag", "only"} (fun k => if k.1 = "tag" then
      Scoped.ObjectSlot.req (Scoped.Term.literal .string "A") else Scoped.ObjectSlot.req
        Scoped.Term.number) none),
    Scoped.Term.object (Scoped.Body.mk {"tag", "shared"} (fun k => if k.1 = "tag" then
      Scoped.ObjectSlot.req (Scoped.Term.literal .string "B") else Scoped.ObjectSlot.req
        Scoped.Term.string) none)])) none))

-- `m.only` is declared by one option, `m.zz` by none, and the store refuses a name on a literal
example : PathRowsC itemM [([.name "m", .name "only"], .someVariants),
    ([.name "m", .name "zz"], .vacant), ([.name "m", .name "tag", .name "x"], .vacant)] := kernel_rfl%

private abbrev two (k v : String) (tk tv : Scoped.Term 0 1 1) : Closed :=
  one (Scoped.Term.object (Scoped.Body.mk {k, v} (fun x => if x.1 = k then
    Scoped.ObjectSlot.req tk else Scoped.ObjectSlot.req tv) none))
private abbrev φA : Closed := one (Scoped.Term.object (Scoped.Body.mk {"tag"} (fun _ =>
  Scoped.ObjectSlot.req (Scoped.Term.literal .string "A")) (some Scoped.Term.opaq)))

-- the clause keeps the option of `A`, which declares no `y`
example : NarrowRowsC [two "tag" "x" (Scoped.Term.literal .string "A") Scoped.Term.number,
    two "tag" "y" (Scoped.Term.literal .string "B") Scoped.Term.number]
    [(φA, [([.name "y"], .vacant)])] := kernel_rfl%

end Calculus
