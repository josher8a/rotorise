import Calculus.Dynamo.Lang.Clause
import Calculus.Dynamo.Analysis.ScopePath

/-!
# The slice of a union of closed codecs

Each option of a union is a closed codec of its own, rooted at its entry, as narrowing roots the
options. A clause reads the body of the root entry of an option: the option is an object, and it
answers at every key that the clause names. The clause and its reading at one name (`AltClause`,
`litSubAt`, `altsSub`) live in `Dynamo/Lang/Clause.lean`, because they read a spec and no term.

A sub-selection keeps each property
of each option and each property of each pair of options. A clause that the options cannot answer
keeps nothing. The extraction and the exclusion partition the options, and the decision over the
graphs (`Closed.viewsDisjoint`) keeps the two halves apart. A kept option holds, at each clause
key, only what the pin of the clause describes.
-/

namespace Calculus

open Alg.Scoped (SlotMode TOp)

section Pin
variable {N : Nat}

/-- The literals of a list of graph terms, where each term is a literal at base `k`. -/
def litsAtG (k : GroundKind) : List (Alg.Scoped.Graph dynSig N) → Option (Finset k.Carrier)
  | [] => some ∅
  | .node (.prim (.literal k' x)) _ :: ts =>
      if h : k' = k then (litsAtG k ts).map (insert (h ▸ x)) else none
  | _ :: _ => none

/-- The alternatives a graph term pins without an adapter: a literal pins itself, and a union of
    literals at one base pins its options. -/
def altsOfG : Alg.Scoped.Graph dynSig N → Option Alts
  | .node (.prim (.literal k x)) _ => some ⟨k, NEFinset.of x ∅⟩
  | .node (.union _) a => match List.ofFn a with
    | .node (.prim (.literal k x)) _ :: ts => (litsAtG k ts).map fun s => ⟨k, NEFinset.of x s⟩
    | _ => none
  | _ => none

/-- **The pin of a graph term**, read through a refinement and through one adapter at the caller
    side `false`. An entry pins nothing. -/
def pinOfG : Alg.Scoped.Graph dynSig N → Option Pin
  | .node (.refine _ _) a => pinOfG (a ())
  | .node (.held false k₀ ks) a => (altsOfG (a true)).map ((k₀ :: ks), ·)
  | t => (altsOfG t).map ([], ·)

end Pin

/-- Whether the caller must write the name of a slot: a fill is required at the caller side. -/
def slotReq : SlotMode dynSig → Bool
  | .opt => false
  | _ => true

/-- **The spec of a closed codec**: the body of its root entry is an object, and each declared
    name gives its presence at the caller side and the pin of its term. -/
def Closed.spec (x : Closed) : Option (MapOf NameSpec) :=
  match x.scopes.graph x.root with
  | .node (.obj fs md _) a => some ⟨fs, fun k => ⟨slotReq (md k), pinOfG (a (.inl k))⟩⟩
  | _ => none

/-- **Whether a clause describes a closed option**: the option is an object, and it answers at
    every key that the clause names. -/
def AltClause.admitsC (c : AltClause) (x : Closed) : Bool :=
  match x.spec with
  | some s => decide (∀ k : {k // k ∈ c.keys}, litSubAt s c k = true)
  | none => false

/-- The form that a closed option pins at a name. -/
def Closed.formAt (x : Closed) (k : Name) : Option (Word × GroundKind) :=
  ((x.spec.bind (·.at k)).bind (·.pin)).map pinForm

/-- **A clause that the closed options can answer**: some option pins each clause key, at the form
    of the pin of the clause. -/
def AltClause.keyedC (c : AltClause) (os : List Closed) : Bool :=
  decide (∀ k : {k // k ∈ c.keys},
    os.any (fun x => decide (x.formAt k.1 = some (pinForm (c.pin k)))) = true)

/-- **The extraction** of closed options: the options that the clause describes, in their order. -/
def AltClause.extractC (c : AltClause) (os : List Closed) : List Closed :=
  os.filter c.admitsC

/-- **The exclusion** of closed options: the complement of the same predicate. -/
def AltClause.excludeC (c : AltClause) (os : List Closed) : List Closed :=
  os.filter (fun x => !c.admitsC x)

/-- **The certificate of closed options**: each pair of options has disjoint views. -/
def certAllC : List Closed → Bool
  | [] => true
  | x :: xs => xs.all (fun y => x.viewsDisjoint y) && certAllC xs

/-! ## The selection -/

/-- **Two clauses select the join of their extracts.** -/
theorem mem_extractC_or (c c' : AltClause) (os : List Closed) (x : Closed) :
    x ∈ os.filter (fun y => c.admitsC y || c'.admitsC y) ↔
      x ∈ c.extractC os ∨ x ∈ c'.extractC os := by
  simp [AltClause.extractC, List.mem_filter, and_or_left]

/-- The extraction keeps options and reorders none. -/
theorem AltClause.extractC_sublist (c : AltClause) (os : List Closed) :
    (c.extractC os).Sublist os := List.filter_sublist

/-- …and the same for the exclusion. -/
theorem AltClause.excludeC_sublist (c : AltClause) (os : List Closed) :
    (c.excludeC os).Sublist os := List.filter_sublist

/-- **A property of each option survives the slice**: each kept option is an option. Typing and
    the obligations of each closed option are such a property, and so is lawfulness. -/
theorem AltClause.forall_extractC (c : AltClause) {os : List Closed} {P : Closed → Prop}
    (h : ∀ x ∈ os, P x) : ∀ x ∈ c.extractC os, P x :=
  fun x hx => h x (List.mem_of_mem_filter hx)

/-- …and the exclusion keeps it, at the complement of the same predicate. -/
theorem AltClause.forall_excludeC (c : AltClause) {os : List Closed} {P : Closed → Prop}
    (h : ∀ x ∈ os, P x) : ∀ x ∈ c.excludeC os, P x :=
  fun x hx => h x (List.mem_of_mem_filter hx)

/-- **A property of each pair of options survives the slice**, because a sub-selection of pairs is
    a selection of pairs. Compatibility of the meanings is such a property, which is the obligation
    of the union. -/
theorem AltClause.pairs_extractC (c : AltClause) {os : List Closed} {R : Closed → Closed → Prop}
    (h : ∀ x ∈ os, ∀ y ∈ os, R x y) : ∀ x ∈ c.extractC os, ∀ y ∈ c.extractC os, R x y :=
  fun x hx y hy => h x (List.mem_of_mem_filter hx) y (List.mem_of_mem_filter hy)

/-- …and the exclusion keeps it. -/
theorem AltClause.pairs_excludeC (c : AltClause) {os : List Closed} {R : Closed → Closed → Prop}
    (h : ∀ x ∈ os, ∀ y ∈ os, R x y) : ∀ x ∈ c.excludeC os, ∀ y ∈ c.excludeC os, R x y :=
  fun x hx y hy => h x (List.mem_of_mem_filter hx) y (List.mem_of_mem_filter hy)

/-- The certificate of closed options, in the pairwise form. -/
theorem pairwise_of_certAllC : ∀ {os : List Closed}, certAllC os = true →
    List.Pairwise (fun x y => x.viewsDisjoint y = true) os
  | [], _ => .nil
  | _ :: _, h => by
      simp only [certAllC, Bool.and_eq_true, List.all_eq_true] at h
      exact .cons (fun u hu => h.1 u hu) (pairwise_of_certAllC h.2)

/-- **The certificate survives the slice**, because it is pairwise. -/
theorem certAllC_sublist {os' os : List Closed} (hs : os'.Sublist os) (h : certAllC os = true) :
    List.Pairwise (fun x y => x.viewsDisjoint y = true) os' :=
  (pairwise_of_certAllC h).sublist hs

/-! ## The clause and the options -/

/-- A clause that describes a closed option reads the spec of the option at each clause key: the
    name is declared, the caller must write it, and its pin lies inside the pin of the clause. -/
theorem AltClause.admitsC_at {c : AltClause} {x : Closed} (h : c.admitsC x = true)
    (k : {k // k ∈ c.keys}) :
    ∃ s ns, x.spec = some s ∧ s.at k.1 = some ns ∧ ns.required = true ∧
      altsSub ns.pin (c.pin k) = true := by
  unfold AltClause.admitsC at h
  split at h
  · rename_i s hs
    have hk := of_decide_eq_true h k
    unfold litSubAt at hk
    split at hk
    · rename_i ns hns
      simp only [Bool.and_eq_true] at hk
      exact ⟨s, ns, hs, hns, hk⟩
    · cases hk
  · cases h

/-- **A clause that describes a closed option is a clause that the options can answer.** -/
theorem AltClause.keyedC_of_admitsC {c : AltClause} {os : List Closed} {x : Closed} (hx : x ∈ os)
    (h : c.admitsC x = true) : c.keyedC os = true := by
  refine decide_eq_true fun k => List.any_eq_true.mpr ⟨x, hx, decide_eq_true ?_⟩
  obtain ⟨s, ns, hs, hns, _, hsub⟩ := c.admitsC_at h k
  obtain ⟨r, hr, hform⟩ := altsSub_form hsub
  simp only [Closed.formAt, hs, Option.bind_some, hns, hr, Option.map_some, hform]

/-- **A clause that the closed options cannot answer describes no option.** -/
theorem AltClause.admitsC_eq_false_of_keyedC_false {c : AltClause} {os : List Closed}
    (hk : c.keyedC os = false) {x : Closed} (hx : x ∈ os) : c.admitsC x = false :=
  Bool.eq_false_iff.mpr fun h => Bool.false_ne_true (hk.symm.trans (c.keyedC_of_admitsC hx h))

/-- **The refusal of a clause hides no answer**: a clause that the closed options cannot answer
    extracts nothing. -/
theorem AltClause.extractC_eq_nil_of_keyedC_false {c : AltClause} {os : List Closed}
    (hk : c.keyedC os = false) : c.extractC os = [] :=
  (List.filter_congr fun _ hx => c.admitsC_eq_false_of_keyedC_false hk hx).trans
    (List.filter_false os)

/-- ...and excludes no option. -/
theorem AltClause.excludeC_eq_self_of_keyedC_false {c : AltClause} {os : List Closed}
    (hk : c.keyedC os = false) : c.excludeC os = os :=
  List.filter_eq_self.mpr fun _ hx => by rw [c.admitsC_eq_false_of_keyedC_false hk hx]; rfl

/-! ## The slice partitions the union -/

/-- **A clause partitions the options, and the join is the union.** The union of a list of closed
    options sends a datum where some option does, so the join of the union of the extraction and
    the union of the exclusion is the union of the options, at each orientation. -/
theorem AltClause.select_extractC_or_excludeC (c : AltClause) (os : List Closed) (α : Table)
    (o : Alg.Orient) (v : Value) :
    ((Alg.select ((c.extractC os).map (·.meaning α)) (·.f o) v).isSome ||
        (Alg.select ((c.excludeC os).map (·.meaning α)) (·.f o) v).isSome) =
      (Alg.select (os.map (·.meaning α)) (·.f o) v).isSome := by
  refine Bool.eq_iff_iff.mpr ?_
  simp only [Bool.or_eq_true, Alg.select_isSome_attempt, List.mem_map, AltClause.extractC,
    AltClause.excludeC, List.mem_filter]
  constructor
  · rintro (⟨_, ⟨x, ⟨hx, _⟩, rfl⟩, h⟩ | ⟨_, ⟨x, ⟨hx, _⟩, rfl⟩, h⟩)
    · exact ⟨_, ⟨x, hx, rfl⟩, h⟩
    · exact ⟨_, ⟨x, hx, rfl⟩, h⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, h⟩
    cases hc : c.admitsC x
    · exact Or.inr ⟨_, ⟨x, ⟨hx, by rw [hc]; rfl⟩, rfl⟩, h⟩
    · exact Or.inl ⟨_, ⟨x, ⟨hx, hc⟩, rfl⟩, h⟩

/-- Two distinct members of a pairwise list are related in one order. -/
theorem pairwise_mem_ne {X : Type} {R : X → X → Prop} :
    ∀ {l : List X}, l.Pairwise R → ∀ {a b : X}, a ∈ l → b ∈ l → a ≠ b → R a b ∨ R b a
  | [], _, _, _, ha, _, _ => nomatch ha
  | x :: xs, h, a, b, ha, hb, hne => by
      obtain ⟨hx, hxs⟩ := List.pairwise_cons.mp h
      rcases List.mem_cons.mp ha with rfl | ha'
      · rcases List.mem_cons.mp hb with rfl | hb'
        · exact absurd rfl hne
        · exact Or.inl (hx b hb')
      · rcases List.mem_cons.mp hb with rfl | hb'
        · exact Or.inr (hx a ha')
        · exact pairwise_mem_ne hxs ha' hb' hne

/-- **The two halves of a certified slice share no datum.** The certificate keeps the views of each
    pair of options apart, so no value is written by an option of each half, and no attribute is
    read by an option of each half. -/
theorem AltClause.extractC_excludeC_apart {c : AltClause} {os : List Closed}
    (hok : certAllC os = true) (α : Table) :
    (∀ v, ((Alg.select ((c.extractC os).map (·.meaning α)) (·.e) v).isSome &&
        (Alg.select ((c.excludeC os).map (·.meaning α)) (·.e) v).isSome) = false) ∧
      ∀ a, ((Alg.select ((c.extractC os).map (·.meaning α)) (·.p) a).isSome &&
        (Alg.select ((c.excludeC os).map (·.meaning α)) (·.p) a).isSome) = false := by
  have key : ∀ {x y : Closed}, x ∈ c.extractC os → y ∈ c.excludeC os →
      x.viewsDisjoint y = true ∨ y.viewsDisjoint x = true := by
    intro x y hx hy
    simp only [AltClause.extractC, AltClause.excludeC, List.mem_filter] at hx hy
    refine pairwise_mem_ne (pairwise_of_certAllC hok) hx.1 hy.1 fun he => ?_
    rw [he] at hx
    have h2 := hy.2
    rw [hx.2] at h2
    exact Bool.noConfusion h2
  have gen : ∀ o : Alg.Orient, (∀ x y : Closed, x.viewsDisjoint y = true → ∀ v,
      (((x.meaning α).f o v).isSome && ((y.meaning α).f o v).isSome) = false) → ∀ v,
      ((Alg.select ((c.extractC os).map (·.meaning α)) (·.f o) v).isSome &&
        (Alg.select ((c.excludeC os).map (·.meaning α)) (·.f o) v).isSome) = false := by
    intro o hs v
    refine Bool.eq_false_iff.mpr fun hb => ?_
    rw [Bool.and_eq_true, Alg.select_isSome_attempt, Alg.select_isSome_attempt] at hb
    obtain ⟨⟨_, hmx, h1⟩, ⟨_, hmy, h2⟩⟩ := hb
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hmx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hmy
    rcases key hx hy with h | h
    · have := hs x y h v
      rw [h1, h2] at this
      exact Bool.noConfusion this
    · have := hs y x h v
      rw [h1, h2] at this
      exact Bool.noConfusion this
  exact ⟨gen .host fun x y h => (Closed.viewsDisjoint_sound h α).1,
    gen .dual fun x y h => (Closed.viewsDisjoint_sound h α).2⟩


/-! ## What the slice keeps

A kept option holds, at each clause key, only what the pin of the clause describes. The meaning of
a closed codec is the meaning of the body of its root entry, so the reading of the spec is a reading
of the meaning. -/

section Keeps
variable {α : Table}

/-- A literal sends a datum at an orientation exactly where the datum is the literal. -/
theorem ground_literal_isSome (k : GroundKind) (x : k.Carrier) (u : Value) :
    ∀ o : Alg.Orient, ((Alg.Mean.ground (B := dynSig) (.literal k x)).f o u).isSome = inL k x u := by
  have hhost : ((Alg.Mean.ground (B := dynSig) (.literal k x)).f .host u).isSome = inL k x u :=
    (Bool.eq_iff_iff.mpr (Alg.PrimAdm.admV_exact (S := dynSyn) (.literal k x) u)).symm
  refine Alg.Orient.both hhost ?_
  rw [← hhost]
  exact congrArg Option.isSome (congrFun (ground_selfdual (.literal k x)) u).symm

variable {N : Nat} {G : Alg.Scoped.GSys (Alg.tables dynSyn.o α dynTableA) N}

/-- Where each term of a list is a literal at one base, a datum that a term of the list sends is
    one of the literals. -/
theorem inL_of_litsAtG {k : GroundKind} {o : Alg.Orient} {u : Value} :
    ∀ {ts : List (Alg.Scoped.Graph dynSig N)} {s : Finset k.Carrier}, litsAtG k ts = some s →
      ∀ t ∈ ts, ((Alg.Scoped.mng _ G t).f o u).isSome = true → ∃ y ∈ s, inL k y u = true
  | [], _, _, _, ht, _ => nomatch ht
  | .node (.prim (.literal k' x)) a :: ts, s, h, t, ht, hu => by
      simp only [litsAtG] at h
      split at h
      · rename_i hk
        subst hk
        obtain ⟨s', hs, rfl⟩ := Option.map_eq_some_iff.mp h
        rcases List.mem_cons.mp ht with rfl | ht'
        · refine ⟨x, Finset.mem_insert_self _ _, ?_⟩
          rw [← ground_literal_isSome k' x u o]
          exact hu
        · obtain ⟨y, hy, hyu⟩ := inL_of_litsAtG hs t ht' hu
          exact ⟨y, Finset.mem_insert.mpr (Or.inr hy), hyu⟩
      · cases h
  | .leaf _ :: _, _, h, _, _, _ => by simp [litsAtG] at h
  | .node (.prim (.base _)) _ :: _, _, h, _, _, _ => by simp [litsAtG] at h
  | .node .opaq _ :: _, _, h, _, _, _ => by simp [litsAtG] at h
  | .node .never _ :: _, _, h, _, _, _ => by simp [litsAtG] at h
  | .node .set _ :: _, _, h, _, _, _ => by simp [litsAtG] at h
  | .node (.list _ _ _) _ :: _, _, h, _, _, _ => by simp [litsAtG] at h
  | .node (.refine _ _) _ :: _, _, h, _, _, _ => by simp [litsAtG] at h
  | .node (.held _ _ _) _ :: _, _, h, _, _, _ => by simp [litsAtG] at h
  | .node (.legacy _) _ :: _, _, h, _, _, _ => by simp [litsAtG] at h
  | .node (.obj _ _ _) _ :: _, _, h, _, _, _ => by simp [litsAtG] at h
  | .node (.union _) _ :: _, _, h, _, _, _ => by simp [litsAtG] at h

/-- **The alternatives that a graph term pins without an adapter hold each datum that the term
    sends**, at each orientation. -/
theorem inLs_of_altsOfG {o : Alg.Orient} {u : Value} {t : Alg.Scoped.Graph dynSig N} {al : Alts}
    (h : altsOfG t = some al) (hu : ((Alg.Scoped.mng _ G t).f o u).isSome = true) :
    inLs al.1 al.2 u = true := by
  unfold altsOfG at h
  split at h
  · rename_i k x _
    cases h
    exact inLs_eq_true.mpr ⟨x, NEFinset.mem_of _ _, (ground_literal_isSome k x u o).symm.trans hu⟩
  · rename_i m a
    split at h
    · rename_i k x b ts hts
      obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp h
      have hl : litsAtG k (List.ofFn a) = some (insert x s) := by
        rw [hts, litsAtG, dif_pos rfl, hs]; rfl
      have hsel := (Alg.select_isSome_attempt _ _ _).mp hu
      obtain ⟨c, hc, hcu⟩ := hsel
      obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hc
      obtain ⟨y, hy, hyu⟩ := inL_of_litsAtG hl (a p) (List.mem_ofFn.mpr ⟨p, rfl⟩) hcu
      exact inLs_eq_true.mpr ⟨y, hy, hyu⟩
    · cases h
  · cases h

/-- **The pin of a graph term holds each attribute that the term reads**: the stored side reads
    the attribute itself, through a refinement and through the inner term of an adapter. -/
theorem inLs_of_pinOfG_dual {u : Value} {t : Alg.Scoped.Graph dynSig N} :
    ∀ {w : Word} {al : Alts}, pinOfG t = some (w, al) →
      ((Alg.Scoped.mng _ G t).f .dual u).isSome = true → inLs al.1 al.2 u = true := by
  induction t with
  | leaf i => intro w al h _; simp [pinOfG, altsOfG] at h
  | node op a ih =>
    intro w al h hu
    cases op
    case refine p pA =>
      have h2 := (Alg.refine2_f_isSome _ _ _ _ _).symm.trans hu
      exact ih () h (Alg.gate_isSome (Bool.and_eq_true _ _ ▸ h2).2)
    case held s k₀ ks =>
      cases s
      · have h2 := (Alg.held1_f_isSome false _ _ _ .dual u).symm.trans hu
        obtain ⟨al', ha, he⟩ := Option.map_eq_some_iff.mp h
        cases he
        exact inLs_of_altsOfG ha (Alg.gate_isSome (Bool.and_eq_true _ _ ▸ h2).2)
      · obtain ⟨al', ha, he⟩ := Option.map_eq_some_iff.mp h
        cases he
        exact inLs_of_altsOfG ha hu
    all_goals
      obtain ⟨al', ha, he⟩ := Option.map_eq_some_iff.mp h
      cases he
      exact inLs_of_altsOfG ha hu

/-- **The pin of a graph term holds the entry image of each value that the term writes**: the
    caller side reads the value through the word of the pin, which is the word of the adapter. -/
theorem inLs_of_pinOfG_host {u : Value} {t : Alg.Scoped.Graph dynSig N} :
    ∀ {w : Word} {al : Alts}, pinOfG t = some (w, al) →
      ((Alg.Scoped.mng _ G t).f .host u).isSome = true → inLs al.1 al.2 ((α.word w).1 u) = true := by
  induction t with
  | leaf i => intro w al h _; simp [pinOfG, altsOfG] at h
  | node op a ih =>
    intro w al h hu
    cases op
    case refine p pA =>
      have h2 := (Alg.refine2_f_isSome _ _ _ _ _).symm.trans hu
      exact ih () h (Alg.gate_isSome (Bool.and_eq_true _ _ ▸ h2).2)
    case held s k₀ ks =>
      cases s
      · have h2 := (Alg.held1_f_isSome false _ _ _ .host u).symm.trans hu
        obtain ⟨al', ha, he⟩ := Option.map_eq_some_iff.mp h
        cases he
        exact inLs_of_altsOfG ha (Alg.gate_isSome (Bool.and_eq_true _ _ ▸ h2).2)
      · obtain ⟨al', ha, he⟩ := Option.map_eq_some_iff.mp h
        cases he
        exact inLs_of_altsOfG ha hu
    all_goals
      obtain ⟨al', ha, he⟩ := Option.map_eq_some_iff.mp h
      cases he
      exact inLs_of_altsOfG ha hu

/-- **The object at the root reads the payload map of the attribute**: a map that the object
    sends at an orientation has a payload that the slot product sends. -/
theorem objAt_of_root {M : Nat} {d : Alg.Scoped.GSys (Alg.tables dynSyn.o α dynTableA) M}
    {fs : Finset String} {md : {x // x ∈ fs} → SlotMode dynSig} {w : Fin 2}
    {a : (Alg.Scoped.TSig dynSig).Pos (TOp.obj fs md w) → Alg.Scoped.Graph dynSig M}
    {o : Alg.Orient} {keys : Finset Name} {g : {n // n ∈ keys} → Attr}
    (h : ((Alg.Scoped.mng _ d (.node (.obj fs md w) a)).f o (.m keys g)).isSome = true) :
    (Alg.objAt (⟨fs, fun k => Alg.Scoped.mkField (B := dynSig) (md k)
        (Alg.Scoped.mng _ d (a (.inl k)))⟩ : MapOf _)
      (Alg.rcOf (Alg.Scoped.restOf w fun p => Alg.Scoped.mng _ d (a (.inr p)))) o
      ⟨keys, g⟩).isSome = true := by
  have h1 : ((Alg.objectCodec dMap.toSummand (⟨fs, fun k => Alg.Scoped.mkField (B := dynSig) (md k)
      (Alg.Scoped.mng _ d (a (.inl k)))⟩ : MapOf _)
      (Alg.Scoped.restOf w fun p => Alg.Scoped.mng _ d (a (.inr p)))).f o (.m keys g)).isSome =
      true := h
  rw [Alg.objectCodec_f, Option.isSome_map] at h1
  exact h1

/-- The spec of a closed codec reads the body of its root entry, an object. -/
theorem Closed.spec_eq_some {x : Closed} {s : MapOf NameSpec} (h : x.spec = some s) :
    ∃ fs md w a, x.scopes.graph x.root = .node (.obj fs md w) a ∧
      s = ⟨fs, fun k => ⟨slotReq (md k), pinOfG (a (.inl k))⟩⟩ := by
  unfold Closed.spec at h
  split at h
  · rename_i fs md w a hg
    cases h
    exact ⟨fs, md, w, a, hg, rfl⟩
  · cases h

/-- **The meaning of a closed codec is the meaning of the body of its root entry.** -/
theorem Closed.meaning_f_root (x : Closed) (o : Alg.Orient) (v : Value) :
    (x.meaning α).f o v = (Alg.Scoped.mng _ (Alg.Scoped.Closed.toG (Alg.tables dynSyn.o α dynTableA)
      x.scopes) (x.scopes.graph x.root)).f o v :=
  congrFun (congrFun (Alg.Scoped.mng_leaf (S := dynSyn)
    (Alg.Scoped.Closed.toG (Alg.tables dynSyn.o α dynTableA) x.scopes) x.root) o) v

/-- **The stored side of the slice.** A kept option reads, at a clause key, only an attribute in
    the alternatives of the clause. -/
theorem AltClause.admitsC_AdmA {c : AltClause} {x : Closed} (h : c.admitsC x = true)
    (k : {k // k ∈ c.keys}) {keys : Finset Name} {g : {n // n ∈ keys} → Attr}
    (ha : x.AdmA α (.m keys g) = true) (hk : k.1 ∈ keys) :
    inLs (c.pin k).2.1 (c.pin k).2.2 (g ⟨k.1, hk⟩) = true := by
  obtain ⟨s, ns, hs, hns, -, hsub⟩ := c.admitsC_at h k
  obtain ⟨fs, md, w, a, hg, rfl⟩ := Closed.spec_eq_some hs
  obtain ⟨hf, rfl⟩ := MapOf.at_eq_some.mp hns
  obtain ⟨w', al, hp, -, hin⟩ := altsSub_inLs hsub
  refine hin _ (inLs_of_pinOfG_dual (α := α)
    (G := Alg.Scoped.Closed.toG (Alg.tables dynSyn.o α dynTableA) x.scopes) hp ?_)
  have h1 : ((x.meaning α).f .dual (.m keys g)).isSome = true := ha
  rw [Closed.meaning_f_root, hg] at h1
  have h2 := (Alg.objAt_isSome.mp (objAt_of_root h1)).2 ⟨k.1, hk⟩
  have hf' : k.1 ∈ fs := hf
  simp only [Alg.entryCodec, MapOf.at, dif_pos hf', Option.bind_some] at h2
  rwa [Alg.Scoped.fieldCodec_mkField (S := dynSyn)] at h2

/-- **The caller side of the slice.** A kept option writes, at a clause key, only a value whose
    entry image under the word of the clause is in the alternatives of the clause. The option
    requires the name at the caller side, so the map holds the name. -/
theorem AltClause.admitsC_Adm {c : AltClause} {x : Closed} (h : c.admitsC x = true)
    (k : {k // k ∈ c.keys}) {keys : Finset Name} {g : {n // n ∈ keys} → Value}
    (hv : ((x.meaning α).e (.m keys g)).isSome = true) :
    ∃ hk : k.1 ∈ keys,
      inLs (c.pin k).2.1 (c.pin k).2.2 ((α.word (c.pin k).1).1 (g ⟨k.1, hk⟩)) = true := by
  obtain ⟨s, ns, hs, hns, hreq, hsub⟩ := c.admitsC_at h k
  obtain ⟨fs, md, w, a, hg, rfl⟩ := Closed.spec_eq_some hs
  obtain ⟨hf, rfl⟩ := MapOf.at_eq_some.mp hns
  obtain ⟨w', al, hp, rfl, hin⟩ := altsSub_inLs hsub
  have h1 : ((x.meaning α).f .host (.m keys g)).isSome = true := hv
  rw [Closed.meaning_f_root, hg] at h1
  have hobj := Alg.objAt_isSome.mp (objAt_of_root h1)
  have hk : k.1 ∈ keys := by
    refine Decidable.byContradiction fun hk => ?_
    have h3 := hobj.1 k.1 hf hk
    have hf' : k.1 ∈ fs := hf
    simp only [MapOf.at, dif_pos hf'] at h3
    simp only at hreq h3
    generalize md ⟨k.1, hf⟩ = m at hreq h3
    cases m
    · exact Bool.noConfusion h3
    · exact Bool.noConfusion hreq
    · exact Bool.noConfusion h3
  refine ⟨hk, hin _ (inLs_of_pinOfG_host
    (G := Alg.Scoped.Closed.toG (Alg.tables dynSyn.o α dynTableA) x.scopes) hp ?_)⟩
  have h2 := hobj.2 ⟨k.1, hk⟩
  have hf' : k.1 ∈ fs := hf
  simp only [Alg.entryCodec, MapOf.at, dif_pos hf', Option.bind_some] at h2
  rwa [Alg.Scoped.fieldCodec_mkField (S := dynSyn)] at h2

end Keeps

/-! ## Vectors -/

private abbrev one (t : Scoped.Term 0 1 0) : Closed :=
  ⟨1, .snoc (c := 0) (n := 1) .nil (fun i => match i with | ⟨0, _⟩ => t), 0⟩

/-- **A clause at a numeral keeps the closed option that pins that numeral**, and not an option
    that pins another one. -/
example : (AltClause.mk {"k"} fun _ => ([], ⟨.number, NEFinset.of (WFNumeral.of "1") ∅⟩)).admitsC
    (one (Scoped.Term.object (Scoped.Body.mk {"k"}
      (fun _ => Scoped.ObjectSlot.req (Scoped.Term.literal .number (WFNumeral.of "1"))) none))) =
    true := by decide

example : (AltClause.mk {"k"} fun _ => ([], ⟨.number, NEFinset.of (WFNumeral.of "1") ∅⟩)).admitsC
    (one (Scoped.Term.object (Scoped.Body.mk {"k"}
      (fun _ => Scoped.ObjectSlot.req (Scoped.Term.literal .number (WFNumeral.of "2"))) none))) =
    false := by decide

end Calculus
