import Calculus.Dynamo.Analysis.Path
import Calculus.Bridge.Kinds

/-!
# The readings of a path row

A path row states the decision of `at` on the host, and the frontier of the model at the path.
`pathRead` compares the two: the host gives a `HostAt`, and the model gives the frontier by
`Alg.Term.at`, or after a clause by `narrowFrames` and the frontier of the rest of the path. A
generated path module states each row through `PathRows` and `NarrowRows`, and the kernel decides
the rows.

**What a row says.** `pathKind` names the decision of a frontier, and each row reads it. A refusal
is no frontier. No codec is a frontier whose frames each have the head `never`. Some options is a
frontier with a `never` head and with another head. One codec is a frontier with no `never` head,
whose frames are one frame. Two declarations is a frontier with no `never` head and two frames.
`kindOf` states the frontier that each decision names, and two declarations hold two frames
(`two_frames_of_ambiguous`).

**Why one codec is also an equation.** The host resolves a node of the term graph of the root,
and the model's frames are subterms of the same printed root. The emitter records each position of
each node in the print, with the binders above the position, and states each frame of the frontier
as the recorded frame of the resolved node at that position. The kernel decides the equation by
definitional equality. A caller's function is a variable of the theorem, so two frames are equal
only where they hold one function. Equal frames have one meaning (`pathRead_resolved_sem`), so a
resolved row certifies the meaning of the host's decision.

**Why the frame and not its head.** A frame is the term at a position with its binder stack, as
`Term.at` gives it: a variable that a step resolves enters its binder again, so a step past a
cycle lands on a position of the print, with the stack of that position. So the frame itself is
the recorded frame on every row, and the law is congruence. The head through `pathHead` would
equate a variable with its binder, and its law would need the unfolding of a binder.

**What `frameSame` reads.** Two frames are one frame where each position holds one datum: one
constructor, variable, field name and slot, primitive, data predicate and adapter word, and one
binder stack. `frameSame` unfolds no binder, so a recursive term and its unfolding are two frames
(`pathKind_unfolding`); the emitter refuses a row where the host resolves two such frames.
`frameSame` reads no function, because a function has no decision, and no fill value, because a
value has no decidable equality. So two refinements by two closures are one frame to `pathKind`
(`pathKind_reads_no_closure`). There the host decides by the identity of the closure, the
equation of a resolved row holds only for one closure, and a row of two declarations has no
certificate.
-/

namespace Calculus

mutual
/-- **Two terms with one datum at each position**, with no binder unfolded. A function and a fill
    value are not read. -/
def sameData : Term → Term → Bool
  | .prim a, .prim b => groundEq a b
  | .opaq, .opaq | .never, .never => true
  | .var i, .var j => decide (i = j)
  | .mu s, .mu t | .set s, .set t | .legacy s _, .legacy t _ => sameData s t
  | .refine s p _, .refine t q _ => sameData s t && predSame p q
  | .held false s P k ks, .held false t Q l ls =>
      sameData s t && sameData P Q && decide (k :: ks = l :: ls)
  | .list p sp sf, .list q tp tf => sameDataL p q && sameDataO sp tp && sameDataL sf tf
  | .union os, .union ps => sameDataL os ps
  | .object b, .object b' => sameDataB b b'
  | _, _ => false
termination_by structural a => a
/-- …of two bodies: one set of names, with slots of one datum. -/
def sameDataB : Body → Body → Bool
  | .mk fs f w, .mk gs g v =>
      decide (∀ k : {k // k ∈ fs}, ∃ h : k.1 ∈ gs, sameDataS (f k) (g ⟨k.1, h⟩) = true) &&
        decide (∀ k : {k // k ∈ gs}, k.1 ∈ fs) && sameDataO w v
termination_by structural b => b
/-- …of two slots: one presence, and terms of one datum. -/
def sameDataS : ObjectSlot → ObjectSlot → Bool
  | .req s, .req t | .optional s, .optional t | .fill s _, .fill t _ => sameData s t
  | _, _ => false
termination_by structural s => s
/-- …of two lists, position by position. -/
def sameDataL : List Term → List Term → Bool
  | [], [] => true
  | s :: ss, t :: ts => sameData s t && sameDataL ss ts
  | _, _ => false
termination_by structural ss => ss
/-- …of two optional terms. -/
def sameDataO : Option Term → Option Term → Bool
  | none, none => true
  | some s, some t => sameData s t
  | _, _ => false
termination_by structural o => o
end

/-- **Two frames that are one frame** to the decision of `at`: terms and binder stacks of one
    datum at each position. -/
def frameSame (f g : Alg.Frame dynSyn) : Bool := sameData f.1 g.1 && sameDataL f.2 g.2

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
  /-- One codec stands at the path: the frontier, each frame at a position of the codec in the
      printed root, with the binders above the position. -/
  | resolved (f : Alg.Frame dynSyn) (fs : List (Alg.Frame dynSyn))

/-- The decision that the host states. -/
def HostAt.kind : HostAt → PathKind
  | .refused => .refused
  | .vacant => .vacant
  | .someVariants => .someVariants
  | .ambiguous => .ambiguous
  | .resolved _ _ => .resolved

/-- **The decision that a frontier names.** A refusal is `none`, and the empty frontier is no
    codec. -/
def pathKind : Option (List (Alg.Frame dynSyn)) → PathKind
  | none => .refused
  | some [] => .vacant
  | some (f :: gs) =>
      kindOf ((f :: gs).any frameNever) ((f :: gs).all frameNever) (gs.all (frameSame f))

/-- **What a row reads**: the decision of the frontier, and the frontier where one codec stands. -/
def pathRead (r : Option (List (Alg.Frame dynSyn))) :
    HostAt → Bool × Option (List (Alg.Frame dynSyn))
  | .resolved _ _ => (decide (pathKind r = .resolved), r)
  | h => (decide (pathKind r = h.kind), none)

/-- **What the host states that a row reads**: its decision, and the frames of the codec where one
    codec stands. -/
def HostAt.claim : HostAt → Bool × Option (List (Alg.Frame dynSyn))
  | .resolved f fs => (true, some (f :: fs))
  | _ => (true, none)

/-- **The rows of the paths into a root**: `Alg.Term.at` at each path reads what the host states. -/
abbrev PathRows (root : Term) (rows : List (List Alg.Seg × HostAt)) : Prop :=
  rows.map (fun r => pathRead (Alg.Term.at root r.1) r.2) = rows.map (·.2.claim)

/-- **The frames after a clause**: the options of the union that `narrow` keeps, each under the
    binder of a recursive union. -/
def narrowFrames (φ : Term) : Term → List (Alg.Frame dynSyn)
  | .union os => (Alg.narrow .dual φ os).map ((·, []))
  | .mu (.union os) => (Alg.narrow .dual φ os).map ((·, [.mu (.union os)]))
  | t => [(t, [])]

/-- **The rows of the clauses at a union**: for each clause, `narrow`, then the frontier of the
    rest of each path reads what the host states. -/
abbrev NarrowRows (u : Term) (rows : List (Term × List (List Alg.Seg × HostAt))) : Prop :=
  rows.map (fun c => c.2.map fun r =>
      pathRead (Alg.atG Alg.Frame.child r.1 (narrowFrames c.1 u)) r.2) =
    rows.map (·.2.map (·.2.claim))

/-! ## One frame is one frame -/

/-- **A primitive is one primitive with itself.** -/
theorem groundEq_refl : ∀ g : Ground, groundEq g g = true
  | .base _ => decide_eq_true rfl
  | .literal _ _ => by rw [groundEq, dif_pos rfl]; exact decide_eq_true rfl

/-- **A predicate is one datum with itself.** -/
theorem predSame_refl : ∀ p : Pred, predSame p p = true
  | .members _ _ | .except _ _ => by
      rw [predSame, dif_pos rfl, Bool.and_eq_true]
      exact ⟨decide_eq_true fun _ hx => hx, decide_eq_true rfl⟩
  | .closure _ => rfl

mutual
/-- **A term is one datum with itself.** -/
theorem sameData_refl : ∀ t : Term, sameData t t = true
  | .prim g => groundEq_refl g
  | .opaq | .never => rfl
  | .var _ => decide_eq_true rfl
  | .mu t | .set t | .legacy t _ => by simp only [sameData]; exact sameData_refl t
  | .refine t p _ => by simp only [sameData, sameData_refl t, predSame_refl p, Bool.and_self]
  | .held false t P _ _ => by
      simp only [sameData, sameData_refl t, sameData_refl P, Bool.true_and]
      exact decide_eq_true trivial
  | .held true _ _ k₀ _ => nomatch k₀.1
  | .list p sp sf => by
      simp only [sameData, sameDataL_refl p, sameDataO_refl sp, sameDataL_refl sf, Bool.and_self]
  | .union os => by simp only [sameData]; exact sameDataL_refl os
  | .object b => by simp only [sameData]; exact sameDataB_refl b
termination_by structural t => t
/-- …a body. -/
theorem sameDataB_refl : ∀ b : Body, sameDataB b b = true
  | .mk _ f w => by
      simp only [sameDataB, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨fun k => ⟨k.2, sameDataS_refl (f k)⟩, fun k => k.2⟩, sameDataO_refl w⟩
termination_by structural b => b
/-- …a slot. -/
theorem sameDataS_refl : ∀ s : ObjectSlot, sameDataS s s = true
  | .req t | .optional t | .fill t _ => by simp only [sameDataS]; exact sameData_refl t
termination_by structural s => s
/-- …a list. -/
theorem sameDataL_refl : ∀ ts : List Term, sameDataL ts ts = true
  | [] => rfl
  | t :: ts => by simp only [sameDataL, sameData_refl t, sameDataL_refl ts, Bool.and_self]
termination_by structural ts => ts
/-- …an optional term. -/
theorem sameDataO_refl : ∀ o : Option Term, sameDataO o o = true
  | none => rfl
  | some t => by simp only [sameDataO]; exact sameData_refl t
termination_by structural o => o
end

/-- **Two frames that `frameSame` separates are two frames.** -/
theorem ne_of_frameSame {f g : Alg.Frame dynSyn} (h : frameSame f g = false) : f ≠ g := by
  rintro rfl
  rw [frameSame, sameData_refl, sameDataL_refl] at h
  exact Bool.noConfusion h

/-- **A frame reads `never` exactly where its head is `never`.** -/
theorem frameNever_iff (f : Alg.Frame dynSyn) :
    frameNever f = true ↔ (pathHead (f.2.length + 2) f).1 = .never := by
  unfold frameNever
  split <;> simp_all

/-- **A frame that is not the first frame**, where some frame is not one frame with the first. -/
theorem exists_ne_of_all_frameSame {f : Alg.Frame dynSyn} :
    ∀ {gs : List (Alg.Frame dynSyn)}, gs.all (frameSame f) = false → ∃ g ∈ gs, g ≠ f
  | [], h => Bool.noConfusion h
  | g :: gs, h => by
      cases hg : frameSame f g
      · exact ⟨g, List.mem_cons_self .., fun he => ne_of_frameSame hg he.symm⟩
      · rw [List.all_cons, hg, Bool.true_and] at h
        obtain ⟨g', hm, hne⟩ := exists_ne_of_all_frameSame h
        exact ⟨g', List.mem_cons_of_mem _ hm, hne⟩

/-- **Two declarations hold two frames.** -/
theorem two_frames_of_ambiguous {r : Option (List (Alg.Frame dynSyn))}
    (h : pathKind r = .ambiguous) : ∃ f gs, r = some (f :: gs) ∧ ∃ g ∈ gs, g ≠ f := by
  rcases r with _ | _ | ⟨f, gs⟩
  · exact PathKind.noConfusion h
  · exact PathKind.noConfusion h
  · refine ⟨f, gs, rfl, exists_ne_of_all_frameSame ?_⟩
    revert h
    simp only [pathKind]
    generalize (f :: gs).any frameNever = a
    generalize (f :: gs).all frameNever = b
    generalize gs.all (frameSame f) = c
    intro h
    rcases a <;> rcases b <;> rcases c <;> first | rfl | exact PathKind.noConfusion h

/-- **A decision of no codec reads `pathKind` alone.** -/
theorem pathRead_decided (r : Option (List (Alg.Frame dynSyn))) (h : HostAt)
    (hr : h.kind ≠ .resolved) : pathRead r h = h.claim ↔ pathKind r = h.kind := by
  rcases h with _ | _ | _ | _ | ⟨f, fs⟩
  all_goals first
    | exact absurd rfl hr
    | exact ⟨fun he => of_decide_eq_true (congrArg Prod.fst he),
        fun hk => congrArg (·, none) (decide_eq_true hk)⟩

/-- **One codec is its frontier**: the frames of the model are one frame, and they are the recorded
    frames, one for one. -/
theorem pathRead_resolved (r : Option (List (Alg.Frame dynSyn))) (f : Alg.Frame dynSyn)
    (fs : List (Alg.Frame dynSyn)) :
    pathRead r (.resolved f fs) = (HostAt.resolved f fs).claim ↔
      pathKind r = .resolved ∧ r = some (f :: fs) :=
  ⟨fun he => ⟨of_decide_eq_true (congrArg Prod.fst he), congrArg Prod.snd he⟩,
    fun ⟨hk, hr⟩ => by rw [pathRead, decide_eq_true hk, hr]; rfl⟩

/-- **A resolved row certifies meaning**: each frame of the frontier denotes what the recorded
    frame of the codec denotes, at every table. -/
theorem pathRead_resolved_sem {r : Option (List (Alg.Frame dynSyn))}
    {f : Alg.Frame dynSyn} {fs : List (Alg.Frame dynSyn)}
    (h : pathRead r (.resolved f fs) = (HostAt.resolved f fs).claim) (α : Table)
    (β : Alg.Table dynSyn.op) :
    (r.getD []).map (Alg.Frame.sem α β) = (f :: fs).map (Alg.Frame.sem α β) := by
  rw [((pathRead_resolved r f fs).mp h).2]; rfl

/-! ## What the decision does not read -/

/-- **No binder is unfolded**: a recursive list and its unfolding are two declarations. -/
theorem pathKind_unfolding :
    pathKind (some [(.mu (.list [] (some (.var 0)) []), []),
      (.list [] (some (.mu (.list [] (some (.var 0)) []))) [], [])]) = .ambiguous :=
  rfl

/-- **No closure is read**: two refinements of `string` by two closures are one codec to the
    decision, and the one admits a string that the other refuses. -/
theorem pathKind_reads_no_closure (α : Table) (β : Alg.Table dynSyn.op) :
    ∃ f g : Alg.Frame dynSyn, pathKind (some [f, g]) = .resolved ∧
      (Alg.Frame.sem α β f).T (.str "") ∧ ¬ (Alg.Frame.sem α β g).T (.str "") := by
  refine ⟨(.refine Term.string (.closure fun _ => true) (), []),
    (.refine Term.string (.closure fun _ => false) (), []), rfl, ?_, ?_⟩
  · exact ⟨rfl, rfl⟩
  · exact fun h => Bool.false_ne_true h.2

end Calculus
