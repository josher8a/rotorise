import Calculus.Lang.Term

/-!
# A path into a store, and the composition of a path law

A path is a list of segments: a name into a map, or a position into a list. `putPath` is the
write of the store at a path. `path_law` composes the law of a write at a path from one law per
segment (`StepLaw`), for any frames. The lemmas on the object codec and on the positions of a list
shape read codecs only, so each form of the codec proves its step laws from them.
-/

namespace Calculus.Alg

/-- A segment of a path: a name into a map, or a position into a list. -/
inductive Seg where
  | name (k : String)
  | pos (i : Nat)

/-! ## The composition: a path law from one law per segment -/

section Compose
variable {F C V : Type} (sem : F → C) (rd : C → V → Prop) (child : Seg → F → Option (List F))
  (getS : Seg → V → Option V) (putS : Seg → V → V → Option V)

/-- The frontier along a path, for any frames. -/
def atG : List Seg → List F → Option (List F)
  | [], fs => some fs
  | s :: π, fs => (fs.mapM (child s)).bind fun gss => atG π gss.flatten

/-- The write at a path, for any store. -/
def putG : List Seg → V → V → Option V
  | [], x, _ => some x
  | [s], x, a => putS s x a
  | s :: π, x, a => (getS s a).bind fun b => (putG π x b).bind fun b' => putS s b' a

/-- **The law of one frame at one segment.** Where the frame reads an attribute, the store refuses
    the segment there, or one child is responsible: the child reads the entry, and a value that
    the child reads keeps the attribute readable when the store puts the value at the segment. -/
def StepLaw (f : F) (s : Seg) : Prop :=
  ∀ gs, child s f = some gs → ∀ A, rd (sem f) A →
    (getS s A = none ∧ ∀ B, putS s B A = none) ∨
    ∃ g ∈ gs, (∀ B, getS s A = some B → rd (sem g) B) ∧
      ∀ B A', putS s B A = some A' → rd (sem g) B → rd (sem f) A'

/-- A frame of a frontier has its children in the next frontier. -/
theorem mem_flatten_of_mapM {s : Seg} :
    ∀ {fs : List F} {gss : List (List F)}, fs.mapM (child s) = some gss →
      ∀ f ∈ fs, ∃ gs, child s f = some gs ∧ ∀ g ∈ gs, g ∈ gss.flatten
  | [], _, _, f, hf => absurd hf (by simp)
  | f₀ :: fs, gss, h, f, hf => by
      simp only [List.mapM_cons, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨gs₀, h₀, gss', h', rfl⟩ := h
      rcases List.mem_cons.mp hf with rfl | hf'
      · exact ⟨gs₀, h₀, fun g hg => List.mem_flatten.mpr ⟨gs₀, List.mem_cons_self, hg⟩⟩
      · obtain ⟨gs, hgs, hsub⟩ := mem_flatten_of_mapM h' f hf'
        exact ⟨gs, hgs, fun g hg => by
          rw [List.flatten_cons]; exact List.mem_append_right _ (hsub g hg)⟩

/-- A frame of the next frontier is a child of a frame of the frontier. -/
theorem child_of_mem_flatten {s : Seg} :
    ∀ {fs : List F} {gss : List (List F)}, fs.mapM (child s) = some gss →
      ∀ g ∈ gss.flatten, ∃ f ∈ fs, ∃ gs, child s f = some gs ∧ g ∈ gs
  | [], gss, h, g, hg => by
      simp only [List.mapM_nil, pure, Option.some.injEq] at h
      subst h; exact absurd hg (by simp)
  | f₀ :: fs, gss, h, g, hg => by
      simp only [List.mapM_cons, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨gs₀, h₀, gss', h', rfl⟩ := h
      rw [List.flatten_cons] at hg
      rcases List.mem_append.mp hg with hg₀ | hg'
      · exact ⟨f₀, List.mem_cons_self, gs₀, h₀, hg₀⟩
      · obtain ⟨f, hf, gs, hc, hgs⟩ := child_of_mem_flatten h' g hg'
        exact ⟨f, List.mem_cons_of_mem _ hf, gs, hc, hgs⟩

/-- **The strong law along a path.** The frames that satisfy `P` keep their law at each segment,
    and their children satisfy `P`. Then an attribute that a frame of `P` reads stays readable
    after the store puts, at the path, a value that every frame of the frontier reads. -/
theorem path_law (P : F → Prop) (hstep : ∀ f s, P f → StepLaw sem rd child getS putS f s)
    (hP : ∀ f s gs, P f → child s f = some gs → ∀ g ∈ gs, P g) :
    ∀ (π : List Seg) (fs res : List F), atG child π fs = some res → (∀ f ∈ fs, P f) →
      ∀ f ∈ fs, ∀ A a A', rd (sem f) A → (∀ g ∈ res, rd (sem g) a) →
        putG getS putS π a A = some A' → rd (sem f) A'
  | [], fs, res, h, _, f, hf, A, a, A', _, ha, hput => by
      simp only [atG, Option.some.injEq] at h
      simp only [putG, Option.some.injEq] at hput
      subst h hput; exact ha f hf
  | [s], fs, res, h, hfs, f, hf, A, a, A', hA, ha, hput => by
      simp only [atG, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨gss, hm, rfl⟩ := h
      obtain ⟨gs, hgs, hsub⟩ := mem_flatten_of_mapM child hm f hf
      simp only [putG] at hput
      rcases hstep f s (hfs f hf) gs hgs A hA with ⟨-, hno⟩ | ⟨g, hg, -, hp⟩
      · rw [hno] at hput; exact nomatch hput
      · exact hp a A' hput (ha g (hsub g hg))
  | s :: s' :: π, fs, res, h, hfs, f, hf, A, a, A', hA, ha, hput => by
      simp only [atG, Option.bind_eq_some_iff] at h
      obtain ⟨gss, hm, hrest⟩ := h
      obtain ⟨gs, hgs, hsub⟩ := mem_flatten_of_mapM child hm f hf
      simp only [putG, Option.bind_eq_some_iff] at hput
      obtain ⟨B, hB, B', hB', hA'⟩ := hput
      rcases hstep f s (hfs f hf) gs hgs A hA with ⟨hn, -⟩ | ⟨g, hg, hget, hp⟩
      · rw [hn] at hB; exact nomatch hB
      · have hgss : ∀ g ∈ gss.flatten, P g := fun g hg' => by
          obtain ⟨f', hf', gs', hc, hg''⟩ := child_of_mem_flatten child hm g hg'
          exact hP f' s gs' (hfs f' hf') hc g hg''
        have ih := path_law P hstep hP (s' :: π) gss.flatten res
          (by simp only [atG, Option.bind_eq_some_iff]; exact hrest) hgss g (hsub g hg) B a B'
          (hget B hB) ha (by simpa only [putG, Option.bind_eq_some_iff] using hB')
        exact hp B' A' hA' ih

end Compose

section Defs
variable (S : Syn) [Sem S]
/-- The member of the container that a segment enters. -/
def Seg.member : Seg → Option S.M
  | .name _ => (Mean.map (B := S.sig)).map (·.μ)
  | .pos _ => (Mean.list (B := S.sig)).map (·.μ)

end Defs

variable {S : Syn} [Sem S]
/-! ## The store side of a path -/

/-- **The write of the store at one name**: the name holds the value, and every other name keeps
    its value. -/
def _root_.Calculus.MapOf.put {V : Type} (m : MapOf V) (k : String) (x : V) : MapOf V :=
  MapOf.ofFun (insert k m.keys) fun j => if j = k then some x else m.at j

/-- A lookup after a write at one name. -/
theorem _root_.Calculus.MapOf.put_at {V : Type} (m : MapOf V) (k : String) (x : V) (j : String) :
    (m.put k x).at j = if j = k then some x else m.at j := by
  unfold MapOf.put
  refine MapOf.at_ofFun (fun j hj => ?_) j
  have hk : j ≠ k := fun h => hj (h ▸ Finset.mem_insert_self _ _)
  have hm : j ∉ m.keys := fun h => hj (Finset.mem_insert.mpr (Or.inr h))
  rw [if_neg hk, MapOf.at_none hm]

/-- **PutGet at the store**: the name reads the value that the write put there. -/
theorem _root_.Calculus.MapOf.put_at_self {V : Type} (m : MapOf V) (k : String) (x : V) :
    (m.put k x).at k = some x := by
  rw [MapOf.put_at, if_pos rfl]

/-- The value at a segment, where the attribute is the container and holds the entry. -/
def getSeg : Seg → S.V → Option S.V
  | .name k, a =>
      match Mean.map (B := S.sig) with
      | some F => (F.p.out a).bind (·.at k)
      | none => none
  | .pos i, a =>
      match Mean.list (B := S.sig) with
      | some L => (L.p.out a).bind (·[i]?)
      | none => none

/-- **The write of the store at a segment.** A name of a map takes the value. A position inside a
    list takes the value, and a position past the end appends the value. The store refuses every
    other attribute. -/
def putSeg : Seg → S.V → S.V → Option S.V
  | .name k, x, a =>
      match Mean.map (B := S.sig) with
      | some F => (F.p.out a).map fun m => F.p.into (m.put k x)
      | none => none
  | .pos i, x, a =>
      match Mean.list (B := S.sig) with
      | some L => (L.p.out a).map fun xs =>
          L.p.into (if i < xs.length then xs.set i x else xs ++ [x])
      | none => none

/-- **The write of the store at a path.** Every segment before the last must hold an entry. -/
def putPath : List Seg → S.V → S.V → Option S.V := putG getSeg putSeg

/-! ## The object at a name -/

section Object
variable {V M : Type} {member : V → M}

/-- **The payload map is defined exactly where every slot answers**, declared or not. -/
theorem objAt_isSome_all {sems : MapOf (FieldSem V M)} {rc? : Option (Codec V M)} {o : Orient}
    {p : MapOf V} :
    (objAt sems rc? o p).isSome ↔ ∀ k, (liftTable sems rc? k o (p.at k)).isSome := by
  unfold objAt objP
  split
  · next h =>
    simp only [Option.isSome_some, true_iff]
    intro k
    rcases Decidable.em (k ∈ sems.keys ∪ p.keys) with hk | hk
    · exact h k hk
    · rw [MapOf.at_none fun h' => hk (Finset.mem_union.mpr (Or.inr h')),
        liftTable_absent (fun h' => hk (Finset.mem_union.mpr (Or.inl h'))) o]
      rfl
  · next h =>
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    exact fun hall => h fun k _ => hall k

variable {sM : Summand (MapOf V) V M member} {sems : MapOf (FieldSem V M)} {rest : RestSem V M}

/-- What the object reads: a map whose payload the slot product reads. -/
theorem object_readable {A : V} :
    ((objectCodec sM sems rest).p A).isSome ↔
      ∃ m, sM.p.out A = some m ∧ (objAt sems (rcOf rest) .dual m).isSome := by
  simp only [objectCodec, objectCodecCore, carriedCodec, Codec.p, Option.isSome_map]
  constructor
  · intro h
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (Option.isSome_of_isSome_bind h)
    rw [hm, Option.bind_some] at h
    exact ⟨m, hm, h⟩
  · rintro ⟨m, hm, h⟩
    rw [hm, Option.bind_some]; exact h

/-- **The object keeps an attribute readable** after the store puts, at one name, a value that
    the entry codec of the name reads. -/
theorem object_put {A A' x : V} {k : String}
    (hA : ((objectCodec sM sems rest).p A).isSome)
    (hput : (sM.p.out A).map (fun m => sM.p.into (m.put k x)) = some A')
    (hx : ((entryCodec sems (rcOf rest) k).bind fun c => c.p x).isSome) :
    ((objectCodec sM sems rest).p A').isSome := by
  obtain ⟨m, hm, hr⟩ := object_readable.mp hA
  rw [hm, Option.map_some] at hput
  cases hput
  refine object_readable.mpr ⟨_, sM.p.out_into _, objAt_isSome_all.mpr fun j => ?_⟩
  have hj := objAt_isSome_all.mp hr j
  rw [MapOf.put_at]
  rcases Decidable.em (j = k) with rfl | hne
  · rw [if_pos rfl]
    simpa only [liftTable, Option.isSome_map] using hx
  · rw [if_neg hne]; exact hj

/-- **The entry codec of a present name reads the value at the name**, where the object reads
    the attribute. -/
theorem object_get {A B : V} {k : String}
    (hA : ((objectCodec sM sems rest).p A).isSome)
    (hget : (sM.p.out A).bind (·.at k) = some B) :
    ((entryCodec sems (rcOf rest) k).bind fun c => c.p B).isSome := by
  obtain ⟨m, hm, hr⟩ := object_readable.mp hA
  rw [hm, Option.bind_some] at hget
  have hj := objAt_isSome_all.mp hr k
  rw [hget] at hj
  simpa only [liftTable, Option.isSome_map] using hj

end Object

section Positions
variable {V M : Type} {member : V → M}

/-- A row that the shape accepts holds the whole fixed head. -/
theorem slots_le_length : ∀ (cs : List (Codec V M)) (tail : Option (Codec V M)) (n : Nat) ds,
    slots cs tail n = some ds → cs.length ≤ n
  | [], _, _, _, _ => Nat.zero_le _
  | _ :: _, _, 0, _, h => nomatch h
  | _ :: cs, tail, n + 1, _, h => by
      obtain ⟨ds', h', -⟩ := Option.map_eq_some_iff.mp h
      have := slots_le_length cs tail n ds' h'
      simp only [List.length_cons]; omega

/-- **The codec of a position**: the codec of the fixed head inside the head, and the tail
    codec past the head. -/
theorem slots_getElem? : ∀ (cs : List (Codec V M)) (tail : Option (Codec V M)) (n : Nat) ds,
    slots cs tail n = some ds → ∀ j, j < n → ds[j]? = if j < cs.length then cs[j]? else tail
  | [], _, 0, _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | [], none, _ + 1, _, h, _, _ => nomatch h
  | [], some c, n + 1, ds, h, j, hj => by
      obtain ⟨ds', h', rfl⟩ := Option.map_eq_some_iff.mp h
      match j with
      | 0 => rfl
      | j + 1 =>
        simp only [List.getElem?_cons_succ, List.length_nil, Nat.not_lt_zero, if_false]
        have := slots_getElem? [] (some c) n ds' h' j (by omega)
        simpa using this
  | _ :: _, _, 0, _, h, _, _ => nomatch h
  | c :: cs, tail, n + 1, ds, h, j, hj => by
      obtain ⟨ds', h', rfl⟩ := Option.map_eq_some_iff.mp h
      match j with
      | 0 => simp
      | j + 1 =>
        simp only [List.getElem?_cons_succ, List.length_cons, Nat.add_lt_add_iff_right]
        exact slots_getElem? cs tail n ds' h' j (by omega)

/-- One more position past the head takes the tail codec. -/
theorem slots_snoc (c : Codec V M) : ∀ (cs : List (Codec V M)) (n : Nat) ds,
    slots cs (some c) n = some ds → slots cs (some c) (n + 1) = some (ds ++ [c])
  | [], n, ds, h => by
      rw [slots_spread] at h ⊢
      cases h
      rw [List.replicate_succ']
  | _ :: _, 0, _, h => nomatch h
  | c' :: cs, n + 1, ds, h => by
      obtain ⟨ds', h', rfl⟩ := Option.map_eq_some_iff.mp h
      rw [slots, slots_snoc c cs n ds' h']
      rfl

/-- A traversal succeeds exactly where the function answers at every entry. -/
theorem traverse_isSome_iff {α β : Type} {f : α → Option β} {xs : List α} :
    (traverse f xs).isSome ↔ ∀ x ∈ xs, (f x).isSome := by
  refine ⟨fun h x hx => ?_, traverse_isSome_of_all⟩
  obtain ⟨ys, hys⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨y, -, hy⟩ := (traverse_eq_some.mp hys).mem_left hx
  rw [hy]; rfl

/-- **What a list reads**: a list whose shape assigns a codec to each position, and each codec
    reads its position. -/
theorem listCodec_p_isSome {sL : Summand (List V) V M member} {pre : List (Codec V M)}
    {sp : Option (Codec V M)} {suf : List (Codec V M)} {A : V} :
    ((listCodec sL pre sp suf).p A).isSome ↔
      ∃ xs ds, sL.p.out A = some xs ∧ slotsL pre sp suf xs.length = some ds ∧
        ∀ q ∈ ds.zip xs, (q.1.p q.2).isSome := by
  simp only [listCodec, carriedCodec, Codec.p, Option.isSome_map, alignL]
  constructor
  · intro h
    obtain ⟨xs, hxs⟩ := Option.isSome_iff_exists.mp (Option.isSome_of_isSome_bind h)
    rw [hxs, Option.bind_some] at h
    obtain ⟨ps, hps⟩ := Option.isSome_iff_exists.mp (Option.isSome_of_isSome_bind h)
    obtain ⟨ds, hds, rfl⟩ := Option.map_eq_some_iff.mp hps
    rw [hps, Option.bind_some] at h
    exact ⟨xs, ds, hxs, hds, traverse_isSome_iff.mp h⟩
  · rintro ⟨xs, ds, hxs, hds, h⟩
    rw [hxs, Option.bind_some, hds, Option.map_some, Option.bind_some]
    exact traverse_isSome_iff.mpr h

/-- A pair of a list zipped with a list that holds one new entry is an old pair, or the new entry
    at its position. -/
theorem mem_zip_set {α β : Type} : ∀ (ds : List α) (xs : List β) (i : Nat) (b : β) (q : α × β),
    q ∈ ds.zip (xs.set i b) → q ∈ ds.zip xs ∨ (ds[i]? = some q.1 ∧ q.2 = b)
  | [], _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, h => by simp at h
  | d :: ds, x :: xs, 0, b, q, h => by
      simp only [List.set_cons_zero, List.zip_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact .inr ⟨rfl, rfl⟩
      · exact .inl (by simp only [List.zip_cons_cons, List.mem_cons]; exact .inr h)
  | d :: ds, x :: xs, i + 1, b, q, h => by
      simp only [List.set_cons_succ, List.zip_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact .inl (by simp)
      · rcases mem_zip_set ds xs i b q h with h' | h'
        · exact .inl (by simp only [List.zip_cons_cons, List.mem_cons]; exact .inr h')
        · exact .inr (by simpa using h')

end Positions

end Calculus.Alg
