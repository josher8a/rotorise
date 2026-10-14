import Calculus.Dynamo.Lang.Clause
import Calculus.Dynamo.Analysis.ScopePath

/-!
# The precondition of a closed clause

A closed clause is a `Closed`: one scope and a root entry. Its precondition reads the graph
term of the root entry, as `Closed.spec` does, and each function below takes the row that the
stored view of the graph term (`viewG` at the dual) takes. The rows: a literal and a union of literals at one base give `in`, a base gives `type`, `opaque` and an
older reader give `exists`, a `held` gives the precondition of its stored side, a refinement over a
term with an adapter gives the precondition of its inner term, and an open object whose slots are
each required gives `type M` and the precondition of each name. Every other graph term refuses.

An entry refuses, as an entry pins nothing in `Closed.spec`. The precondition thus reads no
entry of the graph and recurses on the graph term alone, so its exactness holds at each
environment of the entries.

`Closed.preconditionOfC_exact` states that the precondition holds on an item exactly where the
stored view of the clause admits the attribute at the path. `Closed.narrow_law_precondition` is
the narrowing law over closed codecs with the precondition in place of the admission.
-/

namespace Calculus

open Alg (Seg)
open Alg.Scoped (TOp SlotMode viewG belowTop keyPos Rooted GFrame narrowC)

/-! ## The precondition of a graph term -/

section Pre
variable {N : Nat}

/-- The literal that the stored view of a graph term is, where it is one. -/
def storedLitG : Alg.Scoped.Graph dynSig N → Option ((k : GroundKind) × k.Carrier)
  | .node (.prim (.literal k x)) _ => some ⟨k, x⟩
  | .node (.held s _ _) a => bif s then storedLitG (a false) else storedLitG (a true)
  | _ => none

/-- The literals of the stored views of a list of graph terms, each at the base `k`, or a
    refusal. -/
def storedLitsG (k : GroundKind) : List (Alg.Scoped.Graph dynSig N) → Option (List k.Carrier)
  | [] => some []
  | t :: ts =>
      match storedLitG t with
      | some ⟨k', x⟩ => if h : k' = k then (storedLitsG k ts).map (h ▸ x :: ·) else none
      | none => none

/-- Whether the stored view of a graph term is `opaque`. -/
def storedOpaqG : Alg.Scoped.Graph dynSig N → Bool
  | .node .opaq _ => true
  | .node (.legacy _) _ => true
  | .node (.held s _ _) a => bif s then storedOpaqG (a false) else storedOpaqG (a true)
  | _ => false

/-- Whether an open block is present, and its stored view is `opaque`. -/
def restOpaqG : (s : Fin 2) → (Fin s → Alg.Scoped.Graph dynSig N) → Bool
  | ⟨1, _⟩, a => storedOpaqG (a ⟨0, Nat.one_pos⟩)
  | _, _ => false

/-- **The preconditions of the names of an open object**, each at the path of its name. The
    precondition of a name is `rec` at the name. A slot that is not required refuses, because the
    stored view of a filled slot is optional. -/
def keysPreG {fs : Finset String} (md : {x // x ∈ fs} → SlotMode dynSig) (rest : Bool)
    (rec : {x // x ∈ fs} → List Seg → Option (List Cond)) (π : List Seg) :
    Option (List Cond) :=
  if rest then
    ((keyPos fs).mapM fun x => match md x with
      | .req => rec x (π ++ [Seg.name x.1])
      | _ => none).map List.flatten
  else none

variable (sys : Fin N → Alg.Scoped.Graph dynSig N)

/-- **The precondition of a graph term at a path**, or a refusal (`none`). The stored view
    decides the row. An entry refuses. -/
def termPreG : Alg.Scoped.Graph dynSig N → List Seg → Option (List Cond)
  | .node (.prim (.base k)) _, π => some [⟨π, .type k.member⟩]
  | .node (.prim (.literal k x)) _, π => some [⟨π, .in k x []⟩]
  | .node (.union _) a, π =>
      match List.ofFn a with
      | t :: ts =>
          match storedLitG t with
          | some ⟨k, x⟩ => (storedLitsG k ts).map fun xs => [⟨π, .in k x xs⟩]
          | none => none
      | [] => none
  | .node .opaq _, π => some [⟨π, .exists⟩]
  | .node (.legacy _) _, π => some [⟨π, .exists⟩]
  | .node (.held s _ _) a, π => bif s then termPreG (a false) π else termPreG (a true) π
  | .node (.refine _ _) a, π => if belowTop sys (a ()) then none else termPreG (a ()) π
  | .node (.obj _ md s) a, π =>
      (keysPreG md (restOpaqG s fun p => a (.inr p)) (fun x => termPreG (a (.inl x))) π).map
        (⟨π, .type .M⟩ :: ·)
  | _, _ => none

end Pre

/-- **The precondition of a closed clause at the path of the union.** The root entry of a clause
    is an open object, and its precondition is the precondition of each name. A clause with no name
    refuses below the root: the clause admits each map there, and the empty conjunction admits each
    attribute. At the root the item is a map, so the empty conjunction is the precondition. -/
def Closed.preconditionOfC (φ : Closed) (π : List Seg) : Option (List Cond) :=
  match φ.scope.graph φ.root with
  | .node (.obj fs md s) a =>
      match keyPos fs, π with
      | [], _ :: _ => none
      | _, _ => keysPreG md (restOpaqG s fun p => a (.inr p))
          (fun x => termPreG φ.scope.graph (a (.inl x))) π
  | _ => none

/-! ## The exactness law -/

/-- **A row at a path**: the attribute at the path exists, and the row holds on the attribute. -/
def rowAt (P : Attr → Bool) (π : List Seg) (R : Attr) : Bool :=
  match readPath π R with
  | some A => P A
  | none => false

/-- The row at a name: the attribute at the path is a map that holds the name, and the row holds on
    the entry. -/
theorem rowAt_name (P : Attr → Bool) (π : List Seg) (n : String) (R : Attr) :
    rowAt P (π ++ [.name n]) R = true ↔ ∃ keys g, readPath π R = some (.m keys g) ∧
      ∃ h : n ∈ keys, P (g ⟨n, h⟩) = true := by
  unfold rowAt
  rw [readPath_append]
  cases readPath π R with
  | none => simp
  | some A =>
      cases A with
      | m keys g =>
          simp only [Option.bind_some, getSeg_name, MapOf.at, Option.some.injEq,
            Attr.m.injEq]
          constructor
          · intro h
            rcases Decidable.em (n ∈ keys) with hn | hn
            · rw [dif_pos hn] at h; exact ⟨keys, g, ⟨rfl, HEq.rfl⟩, hn, h⟩
            · rw [dif_neg hn] at h; exact nomatch h
          · rintro ⟨_, _, ⟨rfl, h⟩, hn, ha⟩
            cases h
            rw [dif_pos hn]; exact ha
      | _ => simp [getSeg_name]

/-- **The object codec of required slots and an open block that reads each attribute reads a
    map** whose declared names are each present and read by the codec of the slot. -/
theorem object_reads {fs : Finset String} (cs : {x // x ∈ fs} → Codec) (rc : Codec)
    (hrc : ∀ A, (rc.p A).isSome = true) (A : Attr) :
    ((Alg.objectCodec mS ⟨fs, fun x => .req (cs x)⟩ (.codec rc)).p A).isSome = true ↔
      ∃ keys g, A = .m keys g ∧ ∀ x : {x // x ∈ fs}, ∃ h : x.1 ∈ keys,
        ((cs x).p (g ⟨x.1, h⟩)).isSome = true := by
  rw [Alg.object_readable]
  cases A with
  | m keys g =>
      constructor
      · rintro ⟨m, hm, hm'⟩
        cases hm
        obtain ⟨ha, he⟩ := Alg.objAt_isSome.mp hm'
        refine ⟨keys, g, rfl, fun x => ?_⟩
        have hk : x.1 ∈ keys := Decidable.byContradiction fun hn => by
          have := ha x.1 x.2 hn
          rw [MapOf.at_of_mem (m := ⟨fs, _⟩) x] at this
          exact nomatch this
        refine ⟨hk, ?_⟩
        have := he ⟨x.1, hk⟩
        simp only [Alg.entryCodec, MapOf.at, dif_pos x.2] at this
        exact this
      · rintro ⟨keys', g', he, h⟩
        cases he
        refine ⟨⟨keys, g⟩, rfl, Alg.objAt_isSome.mpr ⟨fun k hk hn => ?_, fun k => ?_⟩⟩
        · exact absurd (h ⟨k, hk⟩).1 hn
        · simp only [Alg.entryCodec, MapOf.at]
          rcases Decidable.em (k.1 ∈ fs) with hk | hk
          · rw [dif_pos hk]
            obtain ⟨_, h'⟩ := h ⟨k.1, hk⟩
            exact h'
          · rw [dif_neg hk]; exact hrc _
  | _ => simp [mS, mA]


/-- **A primitive reads where its row writes**, because each DynamoDB primitive is self-dual. -/
theorem ground_reads (g : Ground) (A : Attr) :
    ((groundCodec g).p A).isSome = Alg.PrimAdm.admV (S := dynSyn) g A := by
  rw [← ground_selfdual]
  exact (Bool.eq_iff_iff.mpr (Alg.PrimAdm.admV_exact (S := dynSyn) g A)).symm

section Exact
variable (α : Table) {N : Nat} (sys : Fin N → Alg.Scoped.Graph dynSig N) (e : Fin N → Codec)

/-- **The stored view of a graph term**, read at the entries `e`. -/
abbrev storedAt (t : Alg.Scoped.Graph dynSig N) : Codec :=
  (viewG sys .dual t).interp (Alg.Scoped.TStep (Alg.tables dynSyn.o α dynTableA)) e

/-- `storedLitG` names the literal that the stored view reads. -/
theorem storedLitG_reads : ∀ {t : Alg.Scoped.Graph dynSig N} {k : GroundKind} {x : k.Carrier},
    storedLitG t = some ⟨k, x⟩ → ∀ A, ((storedAt α sys e t).p A).isSome = inL k x A
  | .node (.prim (.literal k' x')) _, k, x, h, A => by
      simp only [storedLitG, Option.some.injEq] at h; cases h
      exact ground_reads (.literal k' x') A
  | .node (.held false _ _) a, _, _, h, A => storedLitG_reads (t := a true) h A
  | .node (.held true _ _) a, _, _, h, A => storedLitG_reads (t := a false) h A
  | .leaf _, _, _, h, _ | .node (.prim (.base _)) _, _, _, h, _ | .node .opaq _, _, _, h, _
  | .node .never _, _, _, h, _ | .node .set _, _, _, h, _ | .node (.list _ _ _) _, _, _, h, _
  | .node (.refine _ _) _, _, _, h, _ | .node (.legacy _) _, _, _, h, _
  | .node (.obj _ _ _) _, _, _, h, _ | .node (.union _) _, _, _, h, _ => nomatch h

/-- `storedOpaqG` holds where the stored view reads each attribute. -/
theorem storedOpaqG_reads : ∀ {t : Alg.Scoped.Graph dynSig N}, storedOpaqG t = true →
    ∀ A, ((storedAt α sys e t).p A).isSome = true
  | .node .opaq _, _, _ => rfl
  | .node (.legacy _) _, _, _ => rfl
  | .node (.held false _ _) a, h, A => storedOpaqG_reads (t := a true) h A
  | .node (.held true _ _) a, h, A => storedOpaqG_reads (t := a false) h A
  | .leaf _, h, _ | .node (.prim _) _, h, _ | .node .never _, h, _ | .node .set _, h, _
  | .node (.list _ _ _) _, h, _ | .node (.refine _ _) _, h, _ | .node (.obj _ _ _) _, h, _
  | .node (.union _) _, h, _ => nomatch h

/-- `storedLitsG` names the literals that the stored views of the options read. -/
theorem storedLitsG_reads {k : GroundKind} : ∀ {ts : List (Alg.Scoped.Graph dynSig N)}
    {xs : List k.Carrier}, storedLitsG k ts = some xs → ∀ A,
      (ts.any fun t => ((storedAt α sys e t).p A).isSome) = xs.any fun y => inL k y A
  | [], xs, h, A => by simp only [storedLitsG, Option.some.injEq] at h; subst h; rfl
  | t :: ts, xs, h, A => by
      unfold storedLitsG at h
      split at h
      · next k' x hl =>
        split at h
        · next he =>
          subst he
          simp only [Option.map_eq_some_iff] at h
          obtain ⟨ys, hys, rfl⟩ := h
          rw [List.any_cons, List.any_cons, storedLitG_reads α sys e hl A,
            storedLitsG_reads hys A]
        · exact nomatch h
      · exact nomatch h

/-- The stored view of a union reads where the stored view of one option reads. -/
theorem storedAt_union (m : Nat) (a : Fin m → Alg.Scoped.Graph dynSig N) (A : Attr) :
    ((storedAt α sys e (.node (.union m) a)).p A).isSome =
      (List.ofFn a).any fun t => ((storedAt α sys e t).p A).isSome := by
  refine Bool.eq_iff_iff.mpr ((Alg.select_isSome_attempt _ _ _).trans ?_)
  rw [List.any_eq_true]
  constructor
  · rintro ⟨c, hc, hv⟩
    obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hc
    exact ⟨a p, List.mem_ofFn.mpr ⟨p, rfl⟩, hv⟩
  · rintro ⟨t, ht, hv⟩
    obtain ⟨p, rfl⟩ := List.mem_ofFn.mp ht
    exact ⟨_, List.mem_ofFn.mpr ⟨p, rfl⟩, hv⟩

/-- **The stored view of an open object of required slots reads a map** whose declared names are
    each present and read by the stored view of the slot. -/
theorem storedAt_obj {fs : Finset String} {md : {x // x ∈ fs} → SlotMode dynSig} {s : Fin 2}
    {a : (TOp.obj fs md s).Pos → Alg.Scoped.Graph dynSig N} (hmd : ∀ x, md x = .req)
    (hrest : restOpaqG s (fun p => a (.inr p)) = true) (A : Attr) :
    ((storedAt α sys e (.node (.obj fs md s) a)).p A).isSome = true ↔
      ∃ keys g, A = .m keys g ∧ ∀ x : {x // x ∈ fs}, ∃ h : x.1 ∈ keys,
        ((storedAt α sys e (a (.inl x))).p (g ⟨x.1, h⟩)).isSome = true := by
  match s, a, hrest with
  | ⟨1, _⟩, a, hrest =>
    have hf : (fun x => Alg.Scoped.mkField (SlotMode.view .dual (md x))
        (storedAt α sys e (a (.inl x)))) = fun x => .req (storedAt α sys e (a (.inl x))) :=
      funext fun x => by rw [hmd x]; rfl
    show ((Alg.objectCodec mS ⟨fs, fun x => Alg.Scoped.mkField (SlotMode.view .dual (md x))
        (storedAt α sys e (a (.inl x)))⟩ (.codec (storedAt α sys e (a (.inr ⟨0, Nat.one_pos⟩))))).p
        A).isSome = true ↔ _
    rw [hf]
    exact object_reads _ _ (storedOpaqG_reads α sys e hrest) A

/-- The preconditions of the names of an open object hold where the row of each name holds at the
    path of the name, where the precondition of each name is exact for its row. -/
theorem keysPreG_exact {fs : Finset String} {md : {x // x ∈ fs} → SlotMode dynSig} {rest : Bool}
    {rec : {x // x ∈ fs} → List Seg → Option (List Cond)} {P : {x // x ∈ fs} → Attr → Bool}
    (hrec : ∀ x π ys, rec x π = some ys → ∀ R, ys.all (·.eval R) = rowAt (P x) π R)
    {π : List Seg} {gs : List Cond} (h : keysPreG md rest rec π = some gs) :
    rest = true ∧ (∀ x, md x = .req) ∧ ∀ R, (gs.all (·.eval R) = true ↔
      ∀ x, rowAt (P x) (π ++ [Seg.name x.1]) R = true) := by
  unfold keysPreG at h
  cases hr : rest
  · rw [hr] at h; exact nomatch h
  rw [hr] at h
  simp only [if_true, Option.map_eq_some_iff] at h
  obtain ⟨gss, hm, rfl⟩ := h
  have hx : ∀ x : {x // x ∈ fs}, md x = .req ∧ ∃ ys, rec x (π ++ [Seg.name x.1]) = some ys := by
    intro x
    obtain ⟨ys, hy⟩ := isSome_of_mapM hm x (Alg.Scoped.keyPos_complete fs x)
    revert hy
    cases md x with
    | req => exact fun hy => ⟨rfl, ys, hy⟩
    | opt => exact fun hy => nomatch hy
    | fill _ => exact fun hy => nomatch hy
  refine ⟨rfl, fun x => (hx x).1, fun R => ?_⟩
  rw [all_flatten_mapM hm]
  constructor
  · intro hall x
    obtain ⟨hmd, ys, hy⟩ := hx x
    rw [← hrec x _ ys hy R]
    exact hall x (Alg.Scoped.keyPos_complete fs x) ys (by rw [hmd]; exact hy)
  · intro hall x _ ys hy
    rw [(hx x).1] at hy
    rw [hrec x _ ys hy R]
    exact hall x

/-- **The precondition of a graph term is exact**: on each item, the precondition holds where the
    stored view of the term admits the attribute at the path. -/
theorem termPreG_exact : ∀ (t : Alg.Scoped.Graph dynSig N) (π : List Seg) (gs : List Cond),
    termPreG sys t π = some gs →
      ∀ R, gs.all (·.eval R) = rowAt (fun A => ((storedAt α sys e t).p A).isSome) π R
  | .node (.prim (.base k)) _, π, gs, h, R => by
      simp only [termPreG, Option.some.injEq] at h; subst h
      unfold rowAt Cond.eval
      simp only [List.all_cons, List.all_nil, Bool.and_true]
      cases readPath π R with
      | none => rfl
      | some A =>
          simp only [Test.eval]
          exact (ground_reads (.base k) A).symm
  | .node (.prim (.literal k x)) _, π, gs, h, R => by
      simp only [termPreG, Option.some.injEq] at h; subst h
      unfold rowAt Cond.eval
      simp only [List.all_cons, List.all_nil, Bool.and_true]
      cases readPath π R with
      | none => rfl
      | some A =>
          simp only [Test.eval]
          simp only [List.any_cons, List.any_nil, Bool.or_false]
          exact (ground_reads (.literal k x) A).symm
  | .node (.union m) a, π, gs, h, R => by
      unfold termPreG at h
      split at h
      · next t ts hts =>
        split at h
        · next k x hl =>
          simp only [Option.map_eq_some_iff] at h
          obtain ⟨xs, hxs, rfl⟩ := h
          unfold rowAt Cond.eval
          simp only [List.all_cons, List.all_nil, Bool.and_true]
          cases readPath π R with
          | none => rfl
          | some A =>
              simp only [Test.eval]
              refine Eq.trans ?_ (storedAt_union α sys e m a A).symm
              rw [hts, List.any_cons, List.any_cons, storedLitG_reads α sys e hl A,
                storedLitsG_reads α sys e hxs A]
        · exact nomatch h
      · exact nomatch h
  | .node .opaq _, π, gs, h, R => by
      simp only [termPreG, Option.some.injEq] at h; subst h
      unfold rowAt Cond.eval
      simp only [List.all_cons, List.all_nil, Bool.and_true]
      cases readPath π R <;> rfl
  | .node (.legacy _) _, π, gs, h, R => by
      simp only [termPreG, Option.some.injEq] at h; subst h
      unfold rowAt Cond.eval
      simp only [List.all_cons, List.all_nil, Bool.and_true]
      cases readPath π R <;> rfl
  | .node (.held false _ _) a, π, gs, h, R => termPreG_exact (a true) π gs h R
  | .node (.held true _ _) a, π, gs, h, R => termPreG_exact (a false) π gs h R
  | .node (.refine p pA) a, π, gs, h, R => by
      simp only [termPreG] at h
      split at h
      · exact nomatch h
      · next hb =>
        rw [termPreG_exact (a ()) π gs h R]
        have hv : viewG sys .dual (.node (.refine p pA) a) =
            .node (.refine (Alg.Mean.truth false) pA) fun _ => viewG sys .dual (a ()) := by
          simp only [viewG, hb]; rfl
        unfold rowAt
        cases readPath π R with
        | none => rfl
        | some A =>
            show ((storedAt α sys e (a ())).p A).isSome =
              (((viewG sys .dual (.node (.refine p pA) a)).interp _ e).p A).isSome
            rw [hv]
            show _ = ((Alg.refine2 _ _ _).p A).isSome
            rw [Alg.refine2_p_isSome]
            show _ = (true && Alg.gate _ (Alg.Mean.eval (B := dynSig) false (Alg.Mean.truth false)) A)
            rw [show Alg.Mean.eval (B := dynSig) false (Alg.Mean.truth false) = fun _ => true from
              funext fun v => Alg.Mean.eval_truth (B := dynSig) false v, Alg.gate_true]
            rfl
  | .node (.obj fs md s) a, π, gs, h, R => by
      simp only [termPreG, Option.map_eq_some_iff] at h
      obtain ⟨gs', hb, rfl⟩ := h
      obtain ⟨hrest, hmd, hall⟩ := keysPreG_exact
        (P := fun x A => ((storedAt α sys e (a (.inl x))).p A).isSome)
        (fun x π ys hy R => termPreG_exact (a (.inl x)) π ys hy R) hb
      refine Bool.eq_iff_iff.mpr ?_
      rw [List.all_cons, Bool.and_eq_true, hall R]
      unfold rowAt Cond.eval
      cases hR : readPath π R with
      | none => simp
      | some A =>
          rw [storedAt_obj α sys e hmd hrest]
          simp only [Test.eval, decide_eq_true_eq]
          constructor
          · rintro ⟨hm, hk⟩
            cases A with
            | m keys g =>
                refine ⟨keys, g, rfl, fun x => ?_⟩
                obtain ⟨_, _, he, hn, ha⟩ := (rowAt_name _ π x.1 R).mp (hk x)
                rw [hR] at he; cases he; exact ⟨hn, ha⟩
            | _ => exact nomatch hm
          · rintro ⟨keys, g, rfl, hk⟩
            exact ⟨rfl, fun x => (rowAt_name _ π x.1 R).mpr ⟨keys, g, hR, hk x⟩⟩
  | .leaf _, _, _, h, _ | .node .never _, _, _, h, _ | .node .set _, _, _, h, _
  | .node (.list _ _ _) _, _, _, h, _ => nomatch h

end Exact


/-! ## The precondition of a closed clause is exact -/

section Root
variable (α : Table)

/-- **The admission at a path of the stored view of a closed clause**: the attribute at the path
    exists, and the stored view of the clause admits the attribute. -/
def Closed.admAt (φ : Closed) : List Seg → Attr → Bool :=
  rowAt fun A => (((Alg.Scoped.Closed.viewToG (Alg.tables dynSyn.o α dynTableA) .dual
    φ.scope).e φ.root).p A).isSome

/-- The stored view of a closed codec at its root reads as the stored view of the graph term of
    its root entry, at the solution of the view. -/
theorem Closed.view_root (φ : Closed) {t : Alg.Scoped.Graph dynSig φ.N}
    (hg : φ.scope.graph φ.root = t) (A : Attr) :
    ((Alg.Scoped.Closed.viewToG (Alg.tables dynSyn.o α dynTableA) .dual φ.scope).e φ.root).p A =
      (storedAt α φ.scope.graph
        (Alg.Scoped.Closed.viewToG (Alg.tables dynSyn.o α dynTableA) .dual φ.scope).e t).p A := by
  subst hg
  exact congrFun (congrFun
    ((Alg.Scoped.Closed.viewToG (Alg.tables dynSyn.o α dynTableA) .dual φ.scope).fix φ.root)
    .dual) A

/-- **The precondition of a closed clause is exact on an item**: the precondition holds where the
    stored view of the clause admits the attribute at the path. An item is a map. -/
theorem Closed.preconditionOfC_exact {φ : Closed} {π : List Seg} {gs : List Cond}
    (h : φ.preconditionOfC π = some gs)
    (R : Attr) (hitem : ∃ keys g, R = .m keys g) : gs.all (·.eval R) = φ.admAt α π R := by
  unfold Closed.preconditionOfC at h
  split at h
  · next fs md s a hg =>
    have hroot : (π = [] ∨ ∃ k, k ∈ fs) ∧ keysPreG md (restOpaqG s fun p => a (.inr p))
        (fun x => termPreG φ.scope.graph (a (.inl x))) π = some gs := by
      cases hs : keyPos fs with
      | nil =>
          cases π with
          | nil => exact ⟨.inl rfl, by simpa [hs] using h⟩
          | cons s π => simp [hs] at h
      | cons k ks =>
          exact ⟨.inr ⟨k.1, k.2⟩, by simpa [hs] using h⟩
    obtain ⟨hπ, hkg⟩ := hroot
    let e := (Alg.Scoped.Closed.viewToG (Alg.tables dynSyn.o α dynTableA) .dual φ.scope).e
    obtain ⟨hrest, hmd, hall⟩ := keysPreG_exact
      (P := fun x A => ((storedAt α φ.scope.graph e (a (.inl x))).p A).isSome)
      (fun x π ys hy R => termPreG_exact α φ.scope.graph e (a (.inl x)) π ys hy R) hkg
    refine Bool.eq_iff_iff.mpr ?_
    rw [hall R]
    unfold Closed.admAt rowAt
    have hmap : (∀ x : {x // x ∈ fs}, rowAt (fun A => ((storedAt α φ.scope.graph e
        (a (.inl x))).p A).isSome) (π ++ [Seg.name x.1]) R = true) →
        ∃ keys g, readPath π R = some (.m keys g) := fun hk => by
      rcases hπ with rfl | ⟨k, hk'⟩
      · obtain ⟨keys, g, rfl⟩ := hitem; exact ⟨keys, g, rfl⟩
      · obtain ⟨keys, g, hR, -⟩ := (rowAt_name _ π k R).mp (hk ⟨k, hk'⟩)
        exact ⟨keys, g, hR⟩
    constructor
    · intro hk
      obtain ⟨keys, g, hR⟩ := hmap hk
      simp only [hR]
      rw [Closed.view_root α φ hg, storedAt_obj α _ _ hmd hrest]
      refine ⟨keys, g, rfl, fun x => ?_⟩
      obtain ⟨_, _, he, hn, ha⟩ := (rowAt_name _ π x.1 R).mp (hk x)
      rw [hR] at he; cases he; exact ⟨hn, ha⟩
    · intro hA
      cases hR : readPath π R with
      | none => rw [hR] at hA; exact nomatch hA
      | some A =>
          simp only [hR] at hA
          rw [Closed.view_root α φ hg, storedAt_obj α _ _ hmd hrest] at hA
          obtain ⟨keys, g, rfl, hk⟩ := hA
          exact fun x => (rowAt_name _ π x.1 R).mpr ⟨keys, g, hR, hk x⟩
  · exact nomatch h

/-! ## The narrowing law with the precondition -/

/-- **The narrowing law at DynamoDB over closed codecs, with the precondition in place of the
    admission.** Take an item whose attribute at the path of the union is `A`, and on which the
    precondition of the clause holds. No option that narrowing drops reads `A`. A write at a path
    whose frontier the kept options give keeps `A` readable by the options. -/
theorem Closed.narrow_law_precondition {φ : Closed} {os : List Closed}
    (hty : ∀ x ∈ narrowC (S := dynSyn) .dual φ.rooted (os.map Closed.rooted),
      Alg.Scoped.Closed.Typed (Alg.tables dynSyn.o α dynTableA) x.d ∧
        Alg.Scoped.Closed.Obligations (Alg.tables dynSyn.o α dynTableA) x.d)
    (π : List Seg) (res : List (GFrame dynSig))
    (hat : Alg.atG (GFrame.child (S := dynSyn)) π
      ((narrowC (S := dynSyn) .dual φ.rooted (os.map Closed.rooted)).map Rooted.frame) = some res)
    (w : Codec)
    (hw : ∀ g ∈ res, ∀ x a, w.e x = some a →
      ((Alg.Scoped.GFrame.sem (S := dynSyn) (Alg.tables dynSyn.o α dynTableA) g).p a).isSome)
    {pre : List Seg} {gs : List Cond} (hgs : φ.preconditionOfC pre = some gs)
    {R A A' x a : Attr} (hitem : ∃ keys g, R = .m keys g) (hR : readPath pre R = some A)
    (hG : gs.all (·.eval R) = true)
    (hA : (select (os.map (·.meaning α)) (·.p) A).isSome)
    (hx : w.e x = some a) (hput : Alg.putPath (S := dynSyn) π a A = some A') :
    (∀ y ∈ os.map Closed.rooted, y ∉ narrowC (S := dynSyn) .dual φ.rooted (os.map Closed.rooted) →
        (Alg.Scoped.Rooted.meaning (S := dynSyn) (Alg.tables dynSyn.o α dynTableA) y).p A = none) ∧
      (select (os.map (·.meaning α)) (·.p) A').isSome := by
  have hφ : φ.admAt α pre R = true := by
    rw [← Closed.preconditionOfC_exact α hgs R hitem]; exact hG
  unfold Closed.admAt rowAt at hφ
  rw [hR] at hφ
  exact Closed.narrowC_law α hty π res hat w hw hφ hA hx hput

end Root

/-! ## Vectors

Each vector reduces in the kernel. A precondition is shown as its conditions, each a path of names
and a test. A key of a clause reads at the path of the union and then the name. -/

/-- The names of a path. A position shows as `#`. -/
private def names (π : List Seg) : List String := π.map fun | .name k => k | .pos _ => "#"

/-- `in` at a path, over string literals. -/
private def inS (π : List String) (ys : List String) (c : Cond) : Bool :=
  names c.path == π && match c.test with
    | .in .string x xs => x :: xs == ys
    | _ => false

/-- `in` at a path, over numeric literals. -/
private def inN (π : List String) (ys : List WFNumeral) (c : Cond) : Bool :=
  names c.path == π && match c.test with
    | .in .number x xs => decide (x :: xs = ys)
    | _ => false

/-- `type` at a path. -/
private def typeAt (π : List String) (m : Member) (c : Cond) : Bool :=
  names c.path == π && match c.test with
    | .type m' => decide (m' = m)
    | _ => false

/-- `exists` at a path. -/
private def existsAt (π : List String) (c : Cond) : Bool :=
  names c.path == π && match c.test with
    | .exists => true
    | _ => false

/-- Each condition of a precondition against one check each, in order. -/
private def shows (r : Option (List Cond)) (cs : List (Cond → Bool)) : Bool :=
  match r with
  | some gs => gs.length == cs.length && (gs.zip cs).all fun p => p.2 p.1
  | none => false

/-- A closed codec of one entry. -/
private abbrev one (t : Scoped.Term 1 0) : Closed :=
  ⟨1, (fun i => match i with | ⟨0, _⟩ => t), 0⟩

/-- A clause: an open object whose names are each required. -/
private abbrev clauseOf (fs : Finset String) (f : {x // x ∈ fs} → Scoped.Term 1 1) : Closed :=
  one (Scoped.Term.object (Scoped.Body.mk fs (fun x => Scoped.ObjectSlot.req (f x))
    (some Scoped.Term.opaq)))

/-- A clause of one key. -/
private abbrev cl1 (t : Scoped.Term 1 1) : Closed := clauseOf {"k"} fun _ => t

private abbrev litS (s : String) : Scoped.Term 1 1 := Scoped.Term.literal .string s
private abbrev n1 : Scoped.Term 0 0 := Scoped.Term.literal .number (WFNumeral.of "1")
private abbrev n2 : Scoped.Term 0 0 := Scoped.Term.literal .number (WFNumeral.of "2")
/-- `number(1)`: a caller adapter over the literal `N 1`. -/
private abbrev num {w k : Nat} (l : Scoped.Term 0 0) : Scoped.Term w k :=
  Scoped.Term.held false l Scoped.Term.number (.caller 0, false) []
/-- `decimal('1')`: the library text adapter over the literal `N 1`. -/
private abbrev dec {w k : Nat} (l : Scoped.Term 0 0) (s : String) : Scoped.Term w k :=
  Scoped.Term.held false l (Scoped.Term.literal .string s) (.decimalText, false) []
private abbrev m : List Seg := [.name "m"]

-- a string tag
example : shows ((cl1 (litS "A")).preconditionOfC m) [inS ["m", "k"] ["A"]] = true := by decide
-- a string tag of two literals
example : shows ((cl1 (Scoped.Term.union [litS "A", litS "B"])).preconditionOfC m)
    [inS ["m", "k"] ["A", "B"]] = true := by decide
-- a numeric tag: `number(1)` stores `N 1`
example : shows ((cl1 (num n1)).preconditionOfC m) [inN ["m", "k"] [WFNumeral.of "1"]] = true := by
  decide
-- a decimal tag: `decimal('1')` stores `N 1`
example : shows ((cl1 (dec n1 "1")).preconditionOfC m) [inN ["m", "k"] [WFNumeral.of "1"]] = true := by
  decide
-- a union of numeric tags reads through each adapter to one base
example : shows ((cl1 (Scoped.Term.union [num n1, num n2])).preconditionOfC m)
    [inN ["m", "k"] [WFNumeral.of "1", WFNumeral.of "2"]] = true := by decide
-- a presence clause: `opaque` gives `exists`
example : shows ((cl1 Scoped.Term.opaq).preconditionOfC m) [existsAt ["m", "k"]] = true := by decide
-- a base clause: `number` gives `type N`
example : shows ((cl1 Scoped.Term.number).preconditionOfC m) [typeAt ["m", "k"] .N] = true := by decide
-- two keys: a conjunction, in the order of the names
example : shows ((clauseOf {"t", "k"} fun x => if x.1 = "k" then litS "A" else
    Scoped.Term.number).preconditionOfC m) [inS ["m", "k"] ["A"], typeAt ["m", "t"] .N] = true := by
  decide
-- an open object under a key: `type M` and the precondition of its name
example : shows ((cl1 (Scoped.Term.object (Scoped.Body.mk {"z"} (fun _ =>
    Scoped.ObjectSlot.req (litS "Z")) (some Scoped.Term.opaq)))).preconditionOfC [])
    [typeAt ["k"] .M, inS ["k", "z"] ["Z"]] = true := by decide
-- a refinement over an adapter: the stored view keeps the truth, so the inner term decides
example : shows ((cl1 (Scoped.Term.refine (num n1) (.closure fun _ => true) ())).preconditionOfC m)
    [inN ["m", "k"] [WFNumeral.of "1"]] = true := by decide
-- the empty clause: the empty conjunction at the root, and a refusal below the root
example : shows ((clauseOf ∅ fun k => nomatch k.2).preconditionOfC []) [] = true := by decide
example : ((clauseOf ∅ fun k => nomatch k.2).preconditionOfC m).isNone = true := by decide

-- a closed object refuses
example : ((cl1 (Scoped.Term.object (Scoped.Body.mk {"z"} (fun _ =>
    Scoped.ObjectSlot.req Scoped.Term.string) none))).preconditionOfC m).isNone = true := by decide
-- a list with a spread refuses
example : ((cl1 (Scoped.Term.list [] (some Scoped.Term.string) [])).preconditionOfC m).isNone =
    true := by decide
-- a refinement that the stored view keeps refuses
example : ((cl1 (Scoped.Term.refine Scoped.Term.string (.closure fun _ => true) ())).preconditionOfC
    m).isNone = true := by decide
-- an optional slot under a key refuses
example : ((cl1 (Scoped.Term.object (Scoped.Body.mk {"z"} (fun _ =>
    Scoped.ObjectSlot.optional Scoped.Term.string) (some Scoped.Term.opaq)))).preconditionOfC
    m).isNone = true := by decide
-- a union of two bases refuses
example : ((cl1 (Scoped.Term.union [litS "A", Scoped.Term.literal .number (WFNumeral.of "1")])).preconditionOfC
    m).isNone = true := by decide
-- an entry refuses: the precondition reads no entry
example : ((cl1 (Scoped.Term.ref 0)).preconditionOfC m).isNone = true := by decide
-- a clause whose root entry is no object refuses
example : ((one Scoped.Term.string).preconditionOfC m).isNone = true := by decide

end Calculus
