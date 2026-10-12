import Calculus.Lang.ScopeSound
import Calculus.Lang.Path

/-!
# A path into a closed codec, and narrowing on the graph

A frame of a closed codec is a graph term of its DAG of scopes. One segment reads the slot of a
name, the term of a position, the options of a union, and the body of an entry. An entry unfolds
through the graph of its scope, and the bound of the unfoldings is the count of the entries plus
the first step. A term that stores one member apart from the container of the segment gives no
frame, because the store refuses the segment there.

`narrowC` keeps the options whose views the graph decision does not separate from the view of a
clause. Each option is a closed codec with its own root, as the host roots it. A dropped option
reads no datum that the view of the clause reads (`narrowC_drops`), and the narrowed options read
what the options read where the view of the clause reads (`narrowC_reads`).

The strong law over a closed codec (`Closed.strong_law`) reads the lawfulness of each frame from
`Closed.sound`: a typed closed codec that meets its obligations is lawful at each node of its
graph (`Closed.lawfulNodes`).
-/

namespace Calculus.Alg.Scoped

/-! ## The frontier over the graph -/

section Frontier
variable {S : Syn} [Sem S] {N : Nat}

/-- **The member that a node stores**, read from its operation. A leaf stores none. -/
def μG : Graph S.sig N → Option (Mean.Mem (B := S.sig))
  | .leaf _ => none
  | .node (.prim g) _ => (Mean.ground (B := S.sig) g).μ
  | .node .set a =>
      match Mean.set (B := S.sig) with
      | some L => (μG (a ())).bind L.member
      | none => none
  | .node (.list _ _ _) _ => (Mean.list (B := S.sig)).map (·.μ)
  | .node (.held _ _ _) a => μG (a true)
  | .node (.refine _ _) a => μG (a ())
  | .node (.legacy _) a => μG (a ())
  | .node .opaq _ => none
  | .node .never _ => none
  | .node (.obj _ _ _) _ => (Mean.map (B := S.sig)).map (·.μ)
  | .node (.union _) a => unanimous (List.ofFn fun p => μG (a p))

/-- **The store refuses the segment at every attribute that the node reads**: the node stores one
    member, and the member is not the member of the container. -/
def apartG (s : Seg) (t : Graph S.sig N) : Bool :=
  match μG t with
  | some m => !(decide (s.member S = some m))
  | none => false

/-- The term at one position of a list shape, with `bot` past a prefix that has no spread. `none`
    is a refusal: past the prefix with a suffix, the position depends on the length. -/
def listChildG {X : Type} (bot : X) (pre : List X) (sp : Option X) (suf : List X) (i : Nat) :
    Option X :=
  match pre[i]?, suf, sp with
  | some t, _, _ => some t
  | none, [], some t => some t
  | none, [], none => some bot
  | none, _ :: _, _ => none

/-- The children of the options: a refusal where one option refuses. -/
def joinAll {X : Type} : List (Option (List X)) → Option (List X)
  | [] => some []
  | o :: os =>
      match o, joinAll os with
      | some a, some b => some (a ++ b)
      | _, _ => none

/-- **One segment, by structural recursion on the graph term.** `k` answers an entry. -/
def childG (k : Fin N → Option (List (Graph S.sig N))) (s : Seg) :
    Graph S.sig N → Option (List (Graph S.sig N))
  | .leaf j => k j
  | .node .never _ => some []
  | .node .opaq a => some [.node .opaq a]
  | .node (.union _) a => joinAll (List.ofFn fun p => childG k s (a p))
  | .node (.obj fs md w) a =>
      match s with
      | .name n => some [(slotAtG (md := md) a n).2]
      | .pos _ => if apartG s (.node (.obj fs md w) a) then some [] else none
  | .node (.list n sp m) a =>
      match s with
      | .pos i => (listChildG Graph.never (listParts a).1 (listParts a).2.1 (listParts a).2.2 i).map
          fun t => [t]
      | .name _ => if apartG s (.node (.list n sp m) a) then some [] else none
  | t => if apartG s t then some [] else none

/-- One segment, with a bound on the unfoldings of an entry. -/
def childN (sys : Fin N → Graph S.sig N) : Nat → Seg → Graph S.sig N → Option (List (Graph S.sig N))
  | 0, _, _ => none
  | n + 1, s, t => childG (fun j => childN sys n s (sys j)) s t

end Frontier

/-- **A closed codec at a root entry.** -/
structure Rooted (B : Sig) where
  /-- The count of the entries. -/
  N : Nat
  /-- The DAG of scopes. -/
  d : Closed B N
  /-- The root entry. -/
  root : Fin N

/-- **A frame of a walk**: a graph term of a closed codec. -/
structure GFrame (B : Sig) where
  /-- The count of the entries. -/
  N : Nat
  /-- The DAG of scopes. -/
  d : Closed B N
  /-- The term. -/
  t : Graph B N

section Walk
variable {S : Syn} [Sem S]

/-- The frame of the root entry. -/
def Rooted.frame {B : Sig} (r : Rooted B) : GFrame B := ⟨r.N, r.d, .leaf r.root⟩

/-- **The children of a frame at a segment**, in the closed codec of the frame. The bound is the
    count of the entries plus the first step: an unguarded chain of entries visits each entry once. -/
def GFrame.child (s : Seg) (f : GFrame S.sig) : Option (List (GFrame S.sig)) :=
  (childN f.d.graph (f.N + 1) s f.t).map (·.map fun t => ⟨f.N, f.d, t⟩)

/-- **The frames at a path** into a closed codec. A refusal is `none`. -/
def Rooted.at (r : Rooted S.sig) (π : List Seg) : Option (List (GFrame S.sig)) :=
  atG GFrame.child π [r.frame]

variable (τ : (s : Bool) → TableAt S.sig s)

/-- The codec of a frame: its term at the solution of its closed codec. -/
def GFrame.sem (f : GFrame S.sig) : Mean.C S.sig := mng τ (Closed.toG τ f.d) f.t

/-- The codec of a closed codec at its root. -/
def Rooted.meaning (r : Rooted S.sig) : Mean.C S.sig := Closed.meaning τ r.d r.root

/-- The frame of the root denotes the closed codec. -/
theorem Rooted.frame_sem (r : Rooted S.sig) : r.frame.sem τ = r.meaning τ := rfl

end Walk


/-! ## Narrowing by a clause on the graph -/

section Narrow
variable {S : Syn} [Sem S] [Leaf S.sig] (o : Orient)

/-- **Narrowing by a clause on the graph**: the options whose views at the orientation `o` the
    graph decision does not separate from the view of the clause. Each option is a closed codec
    with its own root, and the fuel is the fuel of the two closed codecs. -/
def narrowC (φ : Rooted S.sig) (os : List (Rooted S.sig)) : List (Rooted S.sig) :=
  os.filter fun x => !decG (viewSys φ.d.graph o) (viewSys x.d.graph o)
    ((φ.N * x.N + 1) * (φ.N + x.N + 2)) [] (.leaf φ.root) (.leaf x.root)

variable {o}

/-- An option that narrowing drops is one whose view the decision separates from the view of the
    clause. -/
theorem decG_of_dropped {φ x : Rooted S.sig} {os : List (Rooted S.sig)} (hx : x ∈ os)
    (hd : x ∉ narrowC o φ os) :
    decG (viewSys φ.d.graph o) (viewSys x.d.graph o) ((φ.N * x.N + 1) * (φ.N + x.N + 2)) []
      (.leaf φ.root) (.leaf x.root) = true := by
  unfold narrowC at hd
  rw [List.mem_filter] at hd
  cases h : decG (viewSys φ.d.graph o) (viewSys x.d.graph o) ((φ.N * x.N + 1) * (φ.N + x.N + 2))
    [] (.leaf φ.root) (.leaf x.root)
  · exact absurd ⟨hx, by rw [h]; rfl⟩ hd
  · rfl

variable [Shapes S] [LeafMeet S.sig] [TopLaws S] {τ : (s : Bool) → TableAt S.sig s}

/-- **Narrowing drops only what the clause excludes**: an option that narrowing drops reads no
    datum that the view of the clause reads. -/
theorem narrowC_drops (laws : Laws S o) {φ x : Rooted S.sig} {os : List (Rooted S.sig)}
    (hx : x ∈ os) (hd : x ∉ narrowC o φ os) {v : Mean.V (B := S.sig)}
    (hφ : (((Closed.viewToG τ o φ.d).e φ.root).f o v).isSome = true) :
    ((x.meaning τ).f o v).isSome = false := by
  have hap := apart_of_AB (fun k => decG_sound (dL := Closed.viewToG τ o φ.d)
    (dR := Closed.viewToG τ o x.d) laws _ [] (.leaf φ.root) (.leaf x.root)
    (decG_of_dropped hx hd) k fun _ hq => nomatch hq) v
  cases h2 : ((x.meaning τ).f o v).isSome
  · rfl
  have e2 := view_entries x.d _ x.root v (Nat.le_refl _) h2
  have h3 : ((((Closed.viewToG τ o φ.d).e φ.root).f o v).isSome &&
      (((Closed.viewToG τ o x.d).e x.root).f o v).isSome) = false := hap
  rw [hφ, e2] at h3
  exact nomatch h3

omit [Sem S] [Leaf S.sig] [Shapes S] [LeafMeet S.sig] [TopLaws S] in
/-- A first match over the options that a filter keeps is the first match over all options, where
    each dropped option reads nothing at the input. -/
theorem select_filterR {V M X Y : Type} {run : Codec V M → X → Option Y} {x : X}
    {keep : Rooted S.sig → Bool} {d : Rooted S.sig → Codec V M} :
    ∀ os : List (Rooted S.sig), (∀ r ∈ os, keep r = false → run (d r) x = none) →
      select ((os.filter keep).map d) run x = select (os.map d) run x
  | [], _ => rfl
  | r :: os, h => by
      have ih := select_filterR os fun r' hr' => h r' (List.mem_cons_of_mem _ hr')
      rw [List.filter_cons]
      cases hk : keep r
      · simp only [Bool.false_eq_true, if_false, List.map_cons]
        rw [ih]
        simp only [select, List.find?_cons, h r List.mem_cons_self hk, Option.isSome_none]
      · simp only [if_true, List.map_cons]
        simp only [select, List.find?_cons] at ih ⊢
        split
        · rfl
        · exact ih

/-- **Narrowing is the restriction to the clause**: where the view of the clause reads a datum,
    the narrowed options read what the options read. -/
theorem narrowC_reads (laws : Laws S o) (φ : Rooted S.sig) (os : List (Rooted S.sig))
    {v : Mean.V (B := S.sig)} (hφ : (((Closed.viewToG τ o φ.d).e φ.root).f o v).isSome = true) :
    select ((narrowC o φ os).map (·.meaning τ)) (·.f o) v = select (os.map (·.meaning τ)) (·.f o) v :=
  select_filterR os fun x hx hk => by
    have hd : x ∉ narrowC o φ os := fun h => by
      unfold narrowC at h; rw [List.mem_filter] at h; rw [h.2] at hk; exact nomatch hk
    exact Option.not_isSome_iff_eq_none.mp (by
      rw [narrowC_drops laws hx hd hφ]; exact Bool.false_ne_true)

end Narrow


/-! ## Each node of a typed closed codec is lawful -/

section Lawful
variable {S : Syn} [Sem S] (τ : (s : Bool) → TableAt S.sig s)

/-- **A graph term whose every node is lawful** at the entries `e`. An entry is answered apart. -/
def HL {N : Nat} (e : Fin N → Mean.C S.sig) : Graph S.sig N → Prop
  | .leaf _ => True
  | .node o a => Lawful Mean.mem ((Flat.node o a).interp (TStep τ) e) ∧ ∀ p, HL e (a p)

variable {τ}

/-- A renaming of the entries keeps each node lawful. -/
theorem HL.bind {n m : Nat} (π : Fin n → Fin m) (e : Fin m → Mean.C S.sig) :
    ∀ t : Graph S.sig n, HL τ (fun j => e (π j)) t → HL τ e (t.bind fun j => .leaf (π j))
  | .leaf _, _ => trivial
  | .node o a, h => by
      refine ⟨?_, fun p => HL.bind π e (a p) (h.2 p)⟩
      exact (congrArg (Lawful Mean.mem)
        (Flat.interp_bind (R := TStep τ) e (fun j => .leaf (π j)) (.node o a))).mpr h.1

/-- **Each node of an inlined scope term is lawful.** The term is typed, its obligations hold at
    each stage of lawful approximants, and the approximants agree with the solution below their
    index. The constants are lawful. The node reads the laws of its operation (`TOp.lawful`), and
    a union reads the compatibility of its options through the approximants. -/
theorem HL.inlC {c N : Nat} {κ : Fin c → Mean.C S.sig} (hκ : ∀ j, Lawful Mean.mem (κ j))
    {e : Fin N → Mean.C S.sig} {σc : Fin c → Graph S.sig N}
    (hσc : ∀ j, (σc j).interp (TStep τ) e = κ j) (hσcL : ∀ j, HL τ e (σc j)) {w k : Nat}
    {ρw' : Fin w → Mean.C S.sig} {ρk' : Fin k → Mean.C S.sig} {u : Term S.sig c w k} {T μ}
    (h : Scoped.Typed τ κ ρw' ρk' u T μ) :
    ∀ (σw : Fin w → Graph S.sig N) (σk : Fin k → Graph S.sig N) (ρw : Fin w → Mean.C S.sig)
      (ρk : Fin k → Mean.C S.sig) (stw : Nat → Fin w → Mean.C S.sig)
      (stk : Nat → Fin k → Mean.C S.sig),
      (∀ j, (σw j).interp (TStep τ) e = ρw j) → (∀ j, (σk j).interp (TStep τ) e = ρk j) →
      (∀ j, HL τ e (σw j)) → (∀ j, HL τ e (σk j)) →
      (∀ j, Lawful Mean.mem (ρw j)) → (∀ j, Lawful Mean.mem (ρk j)) →
      (∀ n j, AgreeLe Mean.d n (ρw j) (stw n j)) → (∀ n j, AgreeLe Mean.d n (ρk j) (stk n j)) →
      (∀ n, Scoped.Obligations τ κ (stw n) (stk n) u) →
      HL τ e (u.inlC σw σk σc) ∧ Lawful Mean.mem (SFlat.interp (CStep (TStep τ) c κ) u ρw ρk) := by
  induction h with
  | ref i => exact fun _ _ _ _ _ _ _ _ _ hσkL _ hρk _ _ _ => ⟨hσkL i, hρk i⟩
  | const j => exact fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ⟨hσcL j, hκ j⟩
  | @node w k ρw' ρk' o args T μ r hargs hr ih =>
    intro σw σk ρw ρk stw stk hσw hσk hσwL hσkL hρw hρk hagW hagK hob
    have hS := CStep.lawful (TStep_lawful τ) c κ
    have ihp := fun p => ih p ((TOp.kind o).envW σw) ((TOp.kind o).envK σw σk)
      ((TOp.kind o).envW ρw) ((TOp.kind o).envK ρw ρk) (fun n => (TOp.kind o).envW (stw n))
      (fun n => (TOp.kind o).envK (stw n) (stk n))
      (fun j => by
        have e1 := congrFun (Kind.envW_comp (fun t => t.interp (TStep τ) e) (TOp.kind o) σw) j
        rw [e1, funext hσw])
      (fun j => by
        have e1 := congrFun (Kind.envK_comp (fun t => t.interp (TStep τ) e) (TOp.kind o) σw σk) j
        rw [e1, funext hσw, funext hσk])
      (Kind.envW_all hσwL _) (Kind.envK_all hσwL hσkL _) (Kind.envW_all hρw _)
      (Kind.envK_all hρw hρk _) (fun n => Kind.envW_all2 (hagW n) _)
      (fun n => Kind.envK_all2 (hagW n) (hagK n) _) (fun n => (hob n).1 p)
    have hobl : TOp.obl τ o (fun p => SFlat.interp (CStep (TStep τ) c κ) (args p)
        ((TOp.kind o).envW ρw) ((TOp.kind o).envK ρw ρk)) := by
      cases o with
      | held s k₀ ks => exact (hob 0).2
      | union m =>
        intro p q
        exact compat_of_approx (depth := Mean.d) fun n =>
          ⟨_, _, SFlat.agree hS (args p) _ _ _ _ (hagW n) (hagK n),
            SFlat.agree hS (args q) _ _ _ _ (hagW n) (hagK n), (hob n).2 p q⟩
      | _ => trivial
    have hL : Lawful Mean.mem (TOp.run τ o fun p => SFlat.interp (CStep (TStep τ) c κ) (args p)
        ((TOp.kind o).envW ρw) ((TOp.kind o).envK ρw ρk)) :=
      TOp.lawful τ hr (fun p => (ihp p).2) hobl
    refine ⟨⟨?_, fun p => (ihp p).1⟩, hL⟩
    have e2 : ∀ p, ((args p).inlC ((TOp.kind o).envW σw) ((TOp.kind o).envK σw σk) σc).interp
        (TStep τ) e = SFlat.interp (CStep (TStep τ) c κ) (args p) ((TOp.kind o).envW ρw)
          ((TOp.kind o).envK ρw ρk) := fun p => by
      refine (SFlat.interp_inlC (R := TStep τ) e (args p) _ _ σc).trans ?_
      rw [funext hσc]
      congr 1
      · funext j
        have e1 := congrFun (Kind.envW_comp (fun t => t.interp (TStep τ) e) (TOp.kind o) σw) j
        rw [e1, funext hσw]
      · funext j
        have e1 := congrFun (Kind.envK_comp (fun t => t.interp (TStep τ) e) (TOp.kind o) σw σk) j
        rw [e1, funext hσw, funext hσk]
    exact (congrArg (fun a => Lawful Mean.mem (TOp.run τ o a)) (funext e2)).mpr hL

/-- **The stages of the last scope of a typed closed codec are lawful**, where its obligations
    hold: each stage is lawful by the soundness of the terms at the stage before. -/
theorem Closed.stage_lawful {c n : Nat} (d : Closed S.sig c) (sc : Scope (TSig S.sig) c n)
    (hκ : ∀ j, Lawful Mean.mem (d.sol (TStep τ) Mean.d j))
    (hty : ∀ i, ∃ T μ, Scoped.Typed τ (d.sol (TStep τ) Mean.d) (Closed.top τ d sc)
      (fun j => Closed.top τ d sc (Fin.castLE (Nat.le_of_lt i.isLt) j)) (sc i) T μ)
    (hob : ∀ k, (∀ j, Lawful Mean.mem (Closed.stage τ d sc k j)) →
      ∀ i, Scoped.Obligations τ (d.sol (TStep τ) Mean.d) (Closed.stage τ d sc k)
        (fun j => Closed.stage τ d sc (k + 1) (Fin.castLE (Nat.le_of_lt i.isLt) j)) (sc i)) :
    ∀ k i, Lawful Mean.mem (Closed.stage τ d sc k i) := by
  intro k
  induction k with
  | zero => exact fun _ => Lawful.empty
  | succ k ih =>
    intro ⟨i, hi⟩
    induction i using Nat.strong_induction_on with
    | _ i ihi =>
      obtain ⟨T, μ, ht⟩ := hty ⟨i, hi⟩
      have e := interp_nf (R := CStep (TStep τ) c (d.sol (TStep τ) Mean.d)) sc
        (Closed.stage τ d sc k) ⟨i, hi⟩
      exact (congrArg (Lawful Mean.mem) e).mpr <|
        sound_term τ _ hκ ht ih (fun j => ihi j.val j.isLt _) (hob k ih ⟨i, hi⟩)

/-- **Each node of a typed closed codec that meets its obligations is lawful**, at the solution. -/
theorem Closed.lawfulNodes : ∀ {N : Nat} (d : Closed S.sig N), Closed.Typed τ d →
    Closed.Obligations τ d → ∀ i, HL τ (d.sol (TStep τ) Mean.d) (d.graph i)
  | _, .nil, _, _, i => i.elim0
  | _, .snoc (c := c) (n := n) d sc, hty, hob, i => by
    have hκ := Closed.sound τ d hty.1 hob.1
    have ih := Closed.lawfulNodes d hty.1 hob.1
    have hR := CStep.lawful (TStep_lawful τ) c (d.sol (TStep τ) Mean.d)
    have hst := Closed.stage_lawful d sc hκ hty.2 hob.2
    have hB := nf_contractive hR sc
    have htop : ∀ i, Lawful Mean.mem (Closed.top τ d sc i) :=
      lawful_strat Mean.d_pos hR sc fun k i => hst k i
    refine Fin.addCases (fun m => ?_) (fun i => ?_) i
    · have e1 : (fun j => (DSys.snoc d sc).sol (TStep τ) Mean.d (Fin.castAdd n j)) =
          d.sol (TStep τ) Mean.d := funext fun j => by simp only [DSys.sol, Fin.append_left]
      simp only [DSys.graph, Fin.append_left]
      exact HL.bind _ _ _ (e1 ▸ ih m)
    · simp only [DSys.graph, Fin.append_right]
      obtain ⟨T, μ, ht⟩ := hty.2 i
      exact (HL.inlC hκ (σc := fun j => .leaf (Fin.castAdd n j))
        (fun j => by simp only [Flat.interp, DSys.sol, Fin.append_left]) (fun _ => trivial) ht
        (fun j => .leaf (Fin.natAdd c j))
        (fun j => .leaf (Fin.natAdd c (Fin.castLE (Nat.le_of_lt i.isLt) j)))
        (Closed.top τ d sc) (fun j => Closed.top τ d sc (Fin.castLE (Nat.le_of_lt i.isLt) j))
        (Closed.stage τ d sc)
        (fun k j => Closed.stage τ d sc (k + 1) (Fin.castLE (Nat.le_of_lt i.isLt) j))
        (fun j => by simp only [Flat.interp, DSys.sol, Fin.append_right])
        (fun j => by simp only [Flat.interp, DSys.sol, Fin.append_right])
        (fun _ => trivial) (fun _ => trivial) htop (fun _ => htop _)
        (fun k j => solve_agree Mean.d_pos hB k j)
        (fun k j => (solve_agree Mean.d_pos hB (k + 1) _).mono (Nat.le_succ k))
        (fun k => hob.2 k (hst k) i)).1

end Lawful


/-! ## The step laws over the graph -/

section Steps
variable {S : Syn} [Sem S] {τ : (s : Bool) → TableAt S.sig s} {N : Nat}

/-- **A node that stores one member stores it at every assignment of the entries.** An entry stores
    no member in the syntax, so no assignment decides the member. -/
theorem μG_sound (e : Fin N → Mean.C S.sig) :
    ∀ (t : Graph S.sig N) {m : Mean.Mem (B := S.sig)}, μG t = some m →
      (t.interp (TStep τ) e).μ = some m
  | .leaf _, _, h => nomatch h
  | .node (.prim _) _, _, h => h
  | .node .set a, m, h => by
      simp only [μG] at h
      show (TOp.run τ .set fun p => (a p).interp (TStep τ) e).μ = some m
      simp only [TOp.run]
      revert h
      cases Mean.set (B := S.sig) with
      | none => intro h; exact nomatch h
      | some L =>
        intro h
        obtain ⟨m', hm', h'⟩ := Option.bind_eq_some_iff.mp h
        rw [L.lift_μ]
        exact (μG_sound e (a ()) hm').symm ▸ h'
  | .node (.list _ _ _) a, m, h => by
      simp only [μG] at h
      show (TOp.run τ (.list _ _ _) fun p => (a p).interp (TStep τ) e).μ = some m
      simp only [TOp.run]
      revert h
      cases Mean.list (B := S.sig) with
      | none => intro h; exact nomatch h
      | some L => intro h; exact h
  | .node (.held _ _ _) a, _, h => μG_sound e (a true) h
  | .node (.refine _ _) a, _, h => μG_sound e (a ()) h
  | .node (.legacy _) a, _, h => μG_sound e (a ()) h
  | .node (.obj _ _ _) a, m, h => by
      simp only [μG] at h
      show (TOp.run τ (.obj _ _ _) fun p => (a p).interp (TStep τ) e).μ = some m
      simp only [TOp.run]
      revert h
      cases Mean.map (B := S.sig) with
      | none => intro h; exact nomatch h
      | some F => intro h; exact h
  | .node (.union _) a, m, h => by
      simp only [μG] at h
      show unanimous (List.ofFn fun p => ((a p).interp (TStep τ) e).μ) = some m
      have hall := unanimous_spec h
      have e1 : (List.ofFn fun p => ((a p).interp (TStep τ) e).μ) = List.ofFn fun p => μG (a p) :=
        List.ofFn_inj.mpr (funext fun p => by
          rw [hall _ (List.mem_ofFn.mpr ⟨p, rfl⟩)]
          exact μG_sound e (a p) (hall _ (List.mem_ofFn.mpr ⟨p, rfl⟩)))
      rw [e1]; exact h
  | .node .opaq _, _, h | .node .never _, _, h => nomatch h

/-- **The store refuses a segment apart from the node.** Where a lawful node reads an attribute,
    the attribute carries the member of the node, and no container of the segment carries it. -/
theorem apart_refusesG (e : Fin N → Mean.C S.sig) {t : Graph S.sig N} {s : Seg}
    (hl : Lawful Mean.mem (t.interp (TStep τ) e)) (hap : apartG s t = true) {A : S.V}
    (hA : ((t.interp (TStep τ) e).p A).isSome = true) :
    getSeg s A = none ∧ ∀ B, putSeg s B A = none := by
  unfold apartG at hap
  revert hap
  match hμ : μG t with
  | none => intro hap; exact nomatch hap
  | some m =>
    intro hap
    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hap
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hA
    have hmem : Mean.mem A = m := hl.reads (μG_sound e t hμ) hv
    cases s with
    | name k =>
      simp only [Seg.member] at hap
      simp only [getSeg, putSeg]
      revert hap
      cases Mean.map (B := S.sig) with
      | none => intro _; exact ⟨rfl, fun _ => rfl⟩
      | some F =>
        intro hap
        have hout : F.p.out A = none := by
          rcases ho : F.p.out A with _ | x
          · rfl
          · exact absurd (congrArg some ((Summand.member_of_out (s := F.toSummand)
              (by rw [ho]; rfl)).symm.trans hmem)) hap
        dsimp only; rw [hout]; exact ⟨rfl, fun _ => rfl⟩
    | pos i =>
      simp only [Seg.member] at hap
      simp only [getSeg, putSeg]
      revert hap
      cases Mean.list (B := S.sig) with
      | none => intro _; exact ⟨rfl, fun _ => rfl⟩
      | some L =>
        intro hap
        have hout : L.p.out A = none := by
          rcases ho : L.p.out A with _ | x
          · rfl
          · exact absurd (congrArg some ((Summand.member_of_out (s := L.toSummand)
              (by rw [ho]; rfl)).symm.trans hmem)) hap
        dsimp only; rw [hout]; exact ⟨rfl, fun _ => rfl⟩

variable (τ) in
/-- **The law of one node at one segment**, at a bound on the unfoldings: where the node reads an
    attribute, the store refuses the segment, or one child reads the entry and a value that the
    child reads keeps the attribute readable when the store puts it at the segment. -/
def StepG (d : GSys τ N) (n : Nat) (t : Graph S.sig N) (s : Seg) : Prop :=
  ∀ gs, childN d.sys n s t = some gs → ∀ A, ((mng τ d t).p A).isSome = true →
    (getSeg s A = none ∧ ∀ B, putSeg s B A = none) ∨
    ∃ g ∈ gs, (∀ B, getSeg s A = some B → ((mng τ d g).p B).isSome = true) ∧
      ∀ B A', putSeg s B A = some A' → ((mng τ d g).p B).isSome = true →
        ((mng τ d t).p A').isSome = true

/-- **The entry row**: an entry reads what its body reads, and its children are the children of
    the body, one unfolding down. -/
theorem StepG.leaf (d : GSys τ N) (n : Nat) (j : Fin N) (s : Seg) (h : StepG τ d n (d.sys j) s) :
    StepG τ d (n + 1) (.leaf j) s := by
  have hp : ∀ X, (mng τ d (.leaf j)).p X = (mng τ d (d.sys j)).p X :=
    fun X => congrFun (congrFun (mng_leaf d j) .dual) X
  intro gs hgs A hA
  rw [hp] at hA
  rcases h gs hgs A hA with hr | ⟨g, hg, hget, hput⟩
  · exact Or.inl hr
  · exact Or.inr ⟨g, hg, hget, fun B A' hB hgB => by rw [hp]; exact hput B A' hB hgB⟩

/-- **The bottom row**: the bottom reads no attribute. -/
theorem StepG.never (d : GSys τ N) (n : Nat) (a : (TOp.never (B := S.sig)).Pos → Graph S.sig N)
    (s : Seg) : StepG τ d (n + 1) (.node .never a) s := by
  intro _ _ A hA
  exact absurd hA (by simp [mng, Flat.interp, TStep, TOp.run, Codec.empty])

/-- **The opaque row**: the child is the node, and the identity reads every attribute. -/
theorem StepG.opaq (d : GSys τ N) (n : Nat) (a : (TOp.opaq (B := S.sig)).Pos → Graph S.sig N)
    (s : Seg) : StepG τ d (n + 1) (.node .opaq a) s := by
  intro gs hgs A _
  simp only [childN, childG, Option.some.injEq] at hgs
  subst hgs
  exact Or.inr ⟨_, List.mem_singleton_self _, fun _ _ => rfl, fun _ _ _ _ => rfl⟩

omit [Sem S] in
/-- Each option gives its children to the join. -/
theorem joinAll_sub {X : Type} :
    ∀ {l : List (Option (List X))} {gs}, joinAll l = some gs →
      ∀ o ∈ l, ∃ go, o = some go ∧ ∀ g ∈ go, g ∈ gs
  | [], _, _, o, ho => absurd ho (by simp)
  | o₀ :: os, gs, h, o, ho => by
      cases o₀ with
      | none => exact nomatch h
      | some a =>
        cases hb : joinAll os with
        | none => simp only [joinAll, hb] at h; exact nomatch h
        | some b =>
          simp only [joinAll, hb, Option.some.injEq] at h
          subst h
          rcases List.mem_cons.mp ho with rfl | ho'
          · exact ⟨a, rfl, fun g hg => List.mem_append_left _ hg⟩
          · obtain ⟨go, hgo, hsub⟩ := joinAll_sub hb o ho'
            exact ⟨go, hgo, fun g hg => List.mem_append_right _ (hsub g hg)⟩

/-- **The union row**: where each option keeps its law, the union keeps the law. The option that
    reads the attribute is responsible, and its children are children of the union. -/
theorem StepG.union (d : GSys τ N) (n m : Nat) (a : (TOp.union (B := S.sig) m).Pos → Graph S.sig N)
    (s : Seg) (h : ∀ p, StepG τ d (n + 1) (a p) s) : StepG τ d (n + 1) (.node (.union m) a) s := by
  intro gs hgs A hA
  have hsel : ∀ X, (mng τ d (.node (.union m) a)).p X =
      select (List.ofFn fun p => mng τ d (a p)) (·.f .dual) X := fun _ => rfl
  rw [hsel] at hA
  obtain ⟨c, hc, hcA⟩ := (select_isSome_attempt _ _ _).mp hA
  obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hc
  obtain ⟨go, hgo, hsub⟩ := joinAll_sub hgs _ (List.mem_ofFn.mpr ⟨p, rfl⟩)
  rcases h p go hgo A hcA with hr | ⟨g, hg, hget, hput⟩
  · exact Or.inl hr
  · refine Or.inr ⟨g, hsub g hg, hget, fun B A' hB hgB => ?_⟩
    rw [hsel]
    exact (select_isSome_attempt _ _ _).mpr ⟨_, List.mem_ofFn.mpr ⟨p, rfl⟩, hput B A' hB hgB⟩

/-- **The row of a node that the store refuses at the segment.** The child is a refusal, or the
    node is apart from the segment and its lawful codec reads no attribute that the store accepts
    there. -/
theorem StepG.apart (d : GSys τ N) {n : Nat} {t : Graph S.sig N} {s : Seg}
    (hc : childN d.sys (n + 1) s t = if apartG s t then some [] else none)
    (hl : Lawful Mean.mem (mng τ d t)) : StepG τ d (n + 1) t s := by
  intro gs hgs A hA
  rw [hc] at hgs
  split at hgs
  · next hap => exact Or.inl (apart_refusesG d.e hl hap hA)
  · exact nomatch hgs

end Steps


section Rows2
variable {S : Syn} [Sem S] {τ : (s : Bool) → TableAt S.sig s} {N : Nat}

/-- **The object row**: a node at an object keeps its law at every name. The child is the term of
    the slot of the name. -/
theorem StepG.obj (d : GSys τ N) (n : Nat) {fs : Finset String} {md : {x // x ∈ fs} → SlotMode S.sig}
    {w : Fin 2} (a : (TOp.obj fs md w (B := S.sig)).Pos → Graph S.sig N) (k : String) :
    StepG τ d (n + 1) (.node (.obj fs md w) a) (.name k) := by
  intro gs hgs A hA
  simp only [childN, childG, Option.some.injEq] at hgs
  subst hgs
  replace hA : ((TOp.run τ (.obj fs md w) fun p => mng τ d (a p)).p A).isSome = true := hA
  refine Or.inr ⟨_, List.mem_singleton_self _, ?_, ?_⟩
  · intro B hB
    show ((mng τ d (slotAtG (md := md) a k).2).f .dual B).isSome = true
    rw [← entry_slot (o := .dual) d a k B]
    simp only [getSeg] at hB
    simp only [TOp.run] at hA
    revert hA hB
    rcases hF : (Mean.map (B := S.sig)) with _ | F
    · intro _ hB; exact nomatch hB
    · intro hA hB; exact object_get hA hB
  · intro B A' hput hB
    replace hB : ((mng τ d (slotAtG (md := md) a k).2).f .dual B).isSome = true := hB
    rw [← entry_slot (o := .dual) d a k B] at hB
    show ((TOp.run τ (.obj fs md w) fun p => mng τ d (a p)).p A').isSome = true
    simp only [putSeg] at hput
    simp only [TOp.run] at hA ⊢
    revert hA hput
    rcases hF : (Mean.map (B := S.sig)) with _ | F
    · intro _ hput; exact nomatch hput
    · intro hA hput; exact object_put hA hput hB

/-- **The codec of a position is the codec of the term at the position.** -/
theorem slotsL_listChildG {X : Type} {bot : X} {pre : List X} {sp : Option X} {suf : List X}
    (dm : X → S.C) {i : Nat} {t : X} {n : Nat} {ds : List S.C}
    (ht : listChildG bot pre sp suf i = some t)
    (hs : slotsL (pre.map dm) (sp.map dm) (suf.map dm) n = some ds) (hi : i < n) :
    ds[i]? = some (dm t) := by
  unfold listChildG at ht
  split at ht
  · next t' _ _ hp =>
    cases ht
    obtain ⟨dsF, hF, rfl, hlen, -⟩ := slotsL_split _ _ _ n ds hs
    have hle := slots_le_length _ _ _ _ hF
    have hip : i < (pre.map dm).length := by
      rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp hp).1
    have hiF : i < n - (List.map dm _).length := lt_of_lt_of_le hip hle
    rw [List.getElem?_append_left (by rw [hlen]; exact hiF), slots_getElem? _ _ _ _ hF i hiF,
      if_pos hip, List.getElem?_map, hp]
    rfl
  · next t' hp =>
    cases ht
    rw [List.map_nil, slotsL_nil_suf] at hs
    rw [slots_getElem? _ _ _ _ hs i hi, if_neg (by simpa using hp)]
    rfl
  · next hp =>
    rw [List.map_nil, slotsL_nil_suf] at hs
    have h1 := slots_getElem? _ _ _ _ hs i hi
    rw [if_neg (by simpa using hp)] at h1
    have h2 : i < ds.length := by rw [slots_length _ _ _ _ hs]; exact hi
    rw [List.getElem?_eq_getElem h2] at h1
    exact nomatch h1
  · exact nomatch ht

/-- The codec of a node at a list is the list codec of the codecs of its parts. -/
theorem mng_listCodec (d : GSys τ N) {n m : Nat} {s : Fin 2}
    (a : (TOp.list n s m (B := S.sig)).Pos → Graph S.sig N) {L : ListA S.V S.M Mean.mem Mean.d}
    (hL : Mean.list (B := S.sig) = some L) :
    mng τ d (.node (.list n s m) a) = listCodec L.toSummand ((listParts a).1.map (mng τ d))
      ((listParts a).2.1.map (mng τ d)) ((listParts a).2.2.map (mng τ d)) := by
  show TOp.run τ (.list n s m) (fun p => mng τ d (a p)) = _
  simp only [TOp.run, hL, listParts, List.map_ofFn]
  rw [← optOf_map]
  rfl

/-- **The list row**: a node at a list keeps its law at every position that the shape gives a
    term. The child reads the entry, and a value that the child reads keeps the list readable
    where the store puts the value in place or appends it past the end. -/
theorem StepG.list (d : GSys τ N) (k : Nat) {n m : Nat} {s : Fin 2}
    (a : (TOp.list n s m (B := S.sig)).Pos → Graph S.sig N) (i : Nat) :
    StepG τ d (k + 1) (.node (.list n s m) a) (.pos i) := by
  intro gs hgs A hA
  simp only [childN, childG, Option.map_eq_some_iff] at hgs
  obtain ⟨t, ht, rfl⟩ := hgs
  rcases hL : (Mean.list (B := S.sig)) with _ | L
  · replace hA : ((TOp.run τ (.list n s m) fun p => mng τ d (a p)).p A).isSome = true := hA
    simp only [TOp.run, hL] at hA
    exact absurd hA (by simp [Codec.empty])
  rw [mng_listCodec d a hL] at hA
  obtain ⟨xs, ds, hxs, hds, hall⟩ := listCodec_p_isSome.mp hA
  have hlen := slotsL_length _ _ _ _ _ hds
  refine Or.inr ⟨t, List.mem_singleton_self _, ?_, ?_⟩
  · intro B hB
    simp only [getSeg, hL, hxs, Option.bind_some] at hB
    have hi : i < xs.length := (List.getElem?_eq_some_iff.mp hB).1
    have hdi := slotsL_listChildG (mng τ d) ht hds hi
    rw [List.getElem?_eq_getElem (by omega), Option.some.injEq] at hdi
    rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hB
    have hmem : (ds[i]'(by omega), xs[i]) ∈ ds.zip xs := by
      have h' : i < (ds.zip xs).length := by
        rw [List.length_zip]; exact Nat.lt_min.mpr ⟨by omega, hi⟩
      have := List.getElem_mem h'
      rwa [List.getElem_zip] at this
    have := hall _ hmem
    rwa [hdi, hB] at this
  · intro B A' hput hB
    rw [mng_listCodec d a hL]
    simp only [putSeg, hL, hxs, Option.map_some, Option.some.injEq] at hput
    subst hput
    refine listCodec_p_isSome.mpr ?_
    rcases Nat.lt_or_ge i xs.length with hi | hi
    · rw [if_pos hi]
      refine ⟨_, ds, L.p.out_into _, by rw [List.length_set]; exact hds, fun q hq => ?_⟩
      rcases mem_zip_set ds xs i B q hq with hq' | ⟨hq1, hq2⟩
      · exact hall q hq'
      · rw [slotsL_listChildG (mng τ d) ht hds hi, Option.some.injEq] at hq1
        rw [← hq1, hq2]; exact hB
    · rw [if_neg (Nat.not_lt.mpr hi)]
      obtain ⟨dsF, hF, -, -, -⟩ := slotsL_split _ _ _ _ ds hds
      have hle := slots_le_length _ _ _ _ hF
      simp only [List.length_map] at hle
      unfold listChildG at ht
      split at ht
      · next hp =>
        exact absurd (List.getElem?_eq_some_iff.mp hp).1 (by omega)
      · next t' hp hsuf hsp =>
        cases ht
        rw [hsuf, hsp] at hds
        simp only [Option.map_some, List.map_nil, slotsL_nil_suf] at hds ⊢
        rw [hsuf, hsp]
        simp only [Option.map_some, List.map_nil, slotsL_nil_suf]
        refine ⟨_, ds ++ [mng τ d t], L.p.out_into _, ?_, fun q hq => ?_⟩
        · rw [List.length_append, List.length_singleton]; exact slots_snoc _ _ _ _ hds
        · rw [List.zip_append (by omega)] at hq
          rcases List.mem_append.mp hq with hq' | hq'
          · exact hall q hq'
          · rw [List.zip_cons_cons, List.zip_nil_left, List.mem_singleton] at hq'
            subst hq'; exact hB
      · cases ht
        exact absurd hB (by simp [mng, Graph.never, Flat.interp, TStep, TOp.run, Codec.empty])
      · exact nomatch ht

end Rows2


/-! ## The strong law over a closed codec -/

section Main
variable {S : Syn} [Sem S] {τ : (s : Bool) → TableAt S.sig s} {N : Nat}

/-- **Every node whose nodes are lawful keeps its law** at each segment, at each bound, where each
    entry of the system has lawful nodes. -/
theorem stepG_of_HL (d : GSys τ N) (hsys : ∀ j, HL τ d.e (d.sys j)) :
    ∀ n (t : Graph S.sig N) s, HL τ d.e t → StepG τ d n t s := by
  intro n
  induction n with
  | zero => intro _ _ _ _ hgs; exact nomatch hgs
  | succ n ihn =>
    intro t
    induction t with
    | leaf j => exact fun s _ => StepG.leaf d n j s (ihn _ s (hsys j))
    | node o a ih =>
      intro s h
      have hl : Lawful Mean.mem (mng τ d (.node o a)) := h.1
      cases o with
      | never => exact StepG.never d n a s
      | opaq => exact StepG.opaq d n a s
      | union m => exact StepG.union d n m a s fun p => ih p s (h.2 p)
      | obj fs md w =>
        cases s with
        | name k => exact StepG.obj d n a k
        | pos _ => exact StepG.apart d rfl hl
      | list _ _ _ =>
        cases s with
        | pos i => exact StepG.list d n a i
        | name _ => exact StepG.apart d rfl hl
      | prim _ => exact StepG.apart d rfl hl
      | set => exact StepG.apart d rfl hl
      | held _ _ _ => exact StepG.apart d rfl hl
      | refine _ _ => exact StepG.apart d rfl hl
      | legacy _ => exact StepG.apart d rfl hl

omit [Sem S] in
/-- A term of a list shape is a part of the shape, or the bottom. -/
theorem listChildG_mem {X : Type} {bot : X} {pre : List X} {sp : Option X} {suf : List X} {i : Nat}
    {t : X} (ht : listChildG bot pre sp suf i = some t) : t ∈ pre ∨ sp = some t ∨ t = bot := by
  unfold listChildG at ht
  split at ht
  · next hp => cases ht; exact .inl (List.mem_of_getElem? hp)
  · cases ht; exact .inr (.inl rfl)
  · cases ht; exact .inr (.inr rfl)
  · exact nomatch ht

omit [Sem S] in
/-- A child of the join is a child of one option. -/
theorem joinAll_mem {X : Type} :
    ∀ {l : List (Option (List X))} {gs} {g : X}, joinAll l = some gs → g ∈ gs →
      ∃ o ∈ l, ∃ go, o = some go ∧ g ∈ go
  | [], _, _, h, hg => by
      simp only [joinAll, Option.some.injEq] at h; subst h; exact nomatch hg
  | o₀ :: os, gs, g, h, hg => by
      cases o₀ with
      | none => exact nomatch h
      | some a =>
        cases hb : joinAll os with
        | none => simp only [joinAll, hb] at h; exact nomatch h
        | some b =>
          simp only [joinAll, hb, Option.some.injEq] at h
          subst h
          rcases List.mem_append.mp hg with hga | hgb
          · exact ⟨_, List.mem_cons_self, a, rfl, hga⟩
          · obtain ⟨o, ho, go, hgo, hg'⟩ := joinAll_mem hb hgb
            exact ⟨o, List.mem_cons_of_mem _ ho, go, hgo, hg'⟩

omit [Sem S] in
/-- A count of one gives its one value. -/
theorem optOf_some {X : Type} : ∀ (s : Fin 2) (f : Fin s → X) {t : X}, optOf s f = some t →
    ∃ p, f p = t
  | ⟨0, _⟩, _, _, h => nomatch h
  | ⟨1, _⟩, _, _, h => ⟨_, Option.some.inj h⟩

/-- The bottom has lawful nodes. -/
theorem HL_never (e : Fin N → Mean.C S.sig) : HL τ e (Graph.never (B := S.sig)) :=
  ⟨Lawful.empty, fun p => nomatch p⟩

omit [Sem S] in
/-- A refusal of the store gives no child. -/
theorem mem_of_apart {X : Type} {b : Bool} {gs : List X} {g : X}
    (h : (if b = true then some [] else none) = some gs) (hg : g ∈ gs) : False := by
  split at h
  · cases h; exact nomatch hg
  · exact nomatch h

/-- **The children of a node with lawful nodes have lawful nodes**, where each entry has them. -/
theorem childN_HL (sys : Fin N → Graph S.sig N) (e : Fin N → Mean.C S.sig)
    (hsys : ∀ j, HL τ e (sys j)) :
    ∀ n (t : Graph S.sig N) s gs, childN sys n s t = some gs → HL τ e t → ∀ g ∈ gs, HL τ e g := by
  intro n
  induction n with
  | zero => intro _ _ _ hgs; exact nomatch hgs
  | succ n ihn =>
    intro t
    induction t with
    | leaf j => exact fun s gs hgs _ => ihn (sys j) s gs hgs (hsys j)
    | node o a ih =>
      intro s gs hgs h g hg
      cases o with
      | never =>
        simp only [childN, childG, Option.some.injEq] at hgs
        subst hgs; exact nomatch hg
      | opaq =>
        simp only [childN, childG, Option.some.injEq] at hgs
        subst hgs; rw [List.mem_singleton.mp hg]; exact h
      | union m =>
        obtain ⟨_, hmem, go, rfl, hg'⟩ := joinAll_mem hgs hg
        obtain ⟨p, hp⟩ := List.mem_ofFn.mp hmem
        exact ih p s go hp (h.2 p) g hg'
      | obj fs md w =>
        cases s with
        | name k =>
          simp only [childN, childG, Option.some.injEq] at hgs
          subst hgs
          rw [List.mem_singleton.mp hg]
          unfold slotAtG
          split
          · exact h.2 _
          · match w with
            | ⟨0, _⟩ => exact HL_never e
            | ⟨1, _⟩ => exact h.2 _
        | pos _ => exact (mem_of_apart hgs hg).elim
      | list _ s' _ =>
        cases s with
        | pos i =>
          simp only [childN, childG, Option.map_eq_some_iff] at hgs
          obtain ⟨t, ht, rfl⟩ := hgs
          rw [List.mem_singleton.mp hg]
          rcases listChildG_mem ht with ht' | ht' | rfl
          · obtain ⟨p, rfl⟩ := List.mem_ofFn.mp ht'
            exact h.2 _
          · obtain ⟨p, rfl⟩ := optOf_some _ _ ht'
            exact h.2 _
          · exact HL_never e
        | name _ => exact (mem_of_apart hgs hg).elim
      | prim _ => exact (mem_of_apart hgs hg).elim
      | set => exact (mem_of_apart hgs hg).elim
      | held _ _ _ => exact (mem_of_apart hgs hg).elim
      | refine _ _ => exact (mem_of_apart hgs hg).elim
      | legacy _ => exact (mem_of_apart hgs hg).elim

end Main


section Strong
variable {S : Syn} [Sem S] (τ : (s : Bool) → TableAt S.sig s)

/-- **A lawful frame**: its closed codec is typed and meets its obligations, and its term has
    lawful nodes at the solution. -/
def GFrame.Lawful (f : GFrame S.sig) : Prop :=
  Closed.Typed τ f.d ∧ Closed.Obligations τ f.d ∧ HL τ (f.d.sol (TStep τ) Mean.d) f.t

variable {τ}

/-- **The law of a lawful frame at a segment**, at the bound of `GFrame.child`. -/
theorem GFrame.stepLaw (f : GFrame S.sig) (s : Seg) (hf : GFrame.Lawful τ f) :
    StepLaw (GFrame.sem τ) (fun c A => (c.p A).isSome = true) GFrame.child getSeg putSeg f s := by
  intro gs hgs A hA
  simp only [GFrame.child, Option.map_eq_some_iff] at hgs
  obtain ⟨hs, hch, rfl⟩ := hgs
  rcases stepG_of_HL (Closed.toG τ f.d) (Closed.lawfulNodes f.d hf.1 hf.2.1) (f.N + 1) f.t s
    hf.2.2 hs hch A hA with hr | ⟨g, hg, hget, hput⟩
  · exact Or.inl hr
  · exact Or.inr ⟨⟨f.N, f.d, g⟩, List.mem_map_of_mem hg, hget, hput⟩

/-- **The children of a lawful frame are lawful.** -/
theorem GFrame.child_lawful (f : GFrame S.sig) (s : Seg) (gs : List (GFrame S.sig))
    (hf : GFrame.Lawful τ f) (hc : GFrame.child s f = some gs) : ∀ g ∈ gs, GFrame.Lawful τ g := by
  simp only [GFrame.child, Option.map_eq_some_iff] at hc
  obtain ⟨hs, hch, rfl⟩ := hc
  intro g hg
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
  exact ⟨hf.1, hf.2.1, childN_HL f.d.graph _ (Closed.lawfulNodes f.d hf.1 hf.2.1) (f.N + 1) f.t s
    hs hch hf.2.2 t ht⟩

/-- **The strong law along a path from lawful frames**: an attribute that a lawful frame reads
    stays readable after the store puts, at the path, a value that every frame of the frontier
    reads. -/
theorem GFrame.path_law (π : List Seg) (fs res : List (GFrame S.sig))
    (hat : atG GFrame.child π fs = some res) (hfs : ∀ f ∈ fs, GFrame.Lawful τ f) :
    ∀ f ∈ fs, ∀ A a A', ((f.sem τ).p A).isSome = true →
      (∀ g ∈ res, ((g.sem τ).p a).isSome = true) → putPath π a A = some A' →
        ((f.sem τ).p A').isSome = true :=
  Alg.path_law (GFrame.sem τ) _ GFrame.child getSeg putSeg (GFrame.Lawful τ)
    (fun f s hf => GFrame.stepLaw f s hf) (fun f s gs hf hc => GFrame.child_lawful f s gs hf hc)
    π fs res hat hfs

/-- **The strong law over a closed codec.** Take a typed closed codec that meets its obligations,
    and a writer that agrees with every frame of the frontier at a path. An attribute that the codec
    reads stays readable after the store puts, at the path, what the writer wrote. -/
theorem Closed.strong_law (r : Rooted S.sig) (hty : Closed.Typed τ r.d)
    (hob : Closed.Obligations τ r.d) (π : List Seg) (res : List (GFrame S.sig))
    (hat : r.at π = some res) (w : S.C)
    (hw : ∀ g ∈ res, ∀ x a, w.e x = some a → ((g.sem τ).p a).isSome)
    {A A' x a : S.V} (hA : ((r.meaning τ).p A).isSome) (hx : w.e x = some a)
    (hput : putPath π a A = some A') : ((r.meaning τ).p A').isSome :=
  GFrame.path_law π [r.frame] res hat
    (fun f hf => by rw [List.mem_singleton.mp hf]; exact ⟨hty, hob, trivial⟩)
    r.frame (List.mem_singleton_self _) A a A' hA (fun g hg => hw g hg x a hx) hput

variable [Leaf S.sig] [Shapes S] [LeafMeet S.sig] [TopLaws S]

/-- **The narrowing law over closed codecs.** Take an item that the view of the clause reads. No
    option that narrowing drops reads the item. Where each kept option is typed and meets its
    obligations, a write at a path whose frontier the kept options give keeps the item readable by
    the options. -/
theorem narrowC_law (laws : Laws S .dual) {φ : Rooted S.sig} {os : List (Rooted S.sig)}
    (hty : ∀ x ∈ narrowC .dual φ os, Closed.Typed τ x.d ∧ Closed.Obligations τ x.d)
    (π : List Seg) (res : List (GFrame S.sig))
    (hat : atG GFrame.child π ((narrowC .dual φ os).map Rooted.frame) = some res) (w : S.C)
    (hw : ∀ g ∈ res, ∀ x a, w.e x = some a → ((g.sem τ).p a).isSome)
    {A A' x a : S.V} (hφ : (((Closed.viewToG τ .dual φ.d).e φ.root).p A).isSome = true)
    (hA : (select (os.map (·.meaning τ)) (·.p) A).isSome)
    (hx : w.e x = some a) (hput : putPath π a A = some A') :
    (∀ y ∈ os, y ∉ narrowC .dual φ os → (y.meaning τ).p A = none) ∧
      (select (os.map (·.meaning τ)) (·.p) A').isSome := by
  refine ⟨fun y hy hd => Option.not_isSome_iff_eq_none.mp (by
    rw [narrowC_drops laws hy hd hφ]; exact Bool.false_ne_true), ?_⟩
  rw [← narrowC_reads laws φ os hφ] at hA
  obtain ⟨c, hc, hcA⟩ := (select_isSome_attempt _ _ _).mp hA
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hc
  have h := GFrame.path_law π _ res hat
    (fun f hf => by
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hf
      exact ⟨(hty z hz).1, (hty z hz).2, trivial⟩)
    y.frame (List.mem_map_of_mem hy) A a A' hcA (fun g hg => hw g hg x a hx) hput
  exact (select_isSome_attempt _ _ _).mpr
    ⟨_, List.mem_map_of_mem (List.mem_filter.mp hy).1, h⟩

end Strong

end Calculus.Alg.Scoped
