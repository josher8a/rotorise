import Calculus.Lang.Compat

/-!
# A path into a term, and the strong law of a write at the path

A path is a list of segments: a name into a map, or a position into a list. `Term.at` gives the
frontier of a term at a path: each term that can stand at the path, over its binder stack, or a
refusal. One segment reads the slot of a name, the term of a position, the options of a union, and
the body of a binder. A term that stores one member apart from the container of the segment gives
no term, because the store refuses the segment there.

`putPath` is the write of the store at a path. The strong law (`strong_law`) states that an
attribute that a typed term reads stays readable after the store puts, at the path, a value that
every term of the frontier reads. `path_law` composes the law from one law per segment
(`StepLaw`), and each row of the term language proves its law one time.

A frame under a binder reads the limit of the binder, and the obligations of the body hold at the
stages. So the law reads the frames through `LawfulReach`, and `lawfulReach_of_typed` gives it from
a typed term: lawful approximants agree with each frame at every depth.

`narrow` restricts a union to the options that `Term.disjoint` does not separate from a clause. On
an attribute that the stored admission of the clause admits, the narrowed union reads what the
union reads, and no dropped option reads the attribute (`narrow_law`).
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

/-- **The store refuses the segment on every attribute that the term reads**: the term stores one
    member, and the member is not the member of the container. -/
def apartAt (s : Seg) (t : Term S.sig) : Bool :=
  match μSyn (S := S) t with
  | some m => !(decide (s.member S = some m))
  | none => false

/-- A term with its binder stack: entry `j` is the `mu` that `var j` names, closed over the
    entries after it. -/
abbrev Frame : Type := Term S.sig × List (Term S.sig)

end Defs

variable {S : Syn} [Sem S]

/-- The term at one position of a list shape. `none` is a refusal: past the prefix with a suffix,
    the codec of the position depends on the length, which a path does not carry. Past the prefix
    with no spread, the term is `never`: no readable value has the position. -/
def listChild (pre : List (Term S.sig)) (sp : Option (Term S.sig)) (suf : List (Term S.sig))
    (i : Nat) : Option (Term S.sig) :=
  match pre[i]?, suf, sp with
  | some t, _, _ => some t
  | none, [], some t => some t
  | none, [], none => some .never
  | none, _ :: _, _ => none

mutual
/-- **One segment, by structural recursion on the term.** `none` is a refusal that propagates.
    `k` resolves a variable to its binder, one level up. -/
def childD (k : Term S.sig → List (Term S.sig) → Option (List (Frame S))) (s : Seg)
    (env : List (Term S.sig)) : Term S.sig → Option (List (Frame S))
  | .never => some []
  | .opaq => some [(.opaq, env)]
  | .mu b => childD k s (.mu b :: env) b
  | .var i =>
      match env[i]? with
      | some m => k m (env.drop (i + 1))
      | none => some []
  | .union os => childDL k s env os
  | .object b =>
      match s with
      | .name n => some [((b.slotAt n).term, env)]
      | .pos _ => if apartAt S s (.object b) then some [] else none
  | .list pre sp suf =>
      match s with
      | .pos i => (listChild pre sp suf i).map fun t => [(t, env)]
      | .name _ => if apartAt S s (.list pre sp suf) then some [] else none
  | t => if apartAt S s t then some [] else none
/-- The options of a union: the children of every option, and a refusal if one option refuses. -/
def childDL (k : Term S.sig → List (Term S.sig) → Option (List (Frame S))) (s : Seg)
    (env : List (Term S.sig)) : List (Term S.sig) → Option (List (Frame S))
  | [] => some []
  | t :: ts =>
      match childD k s env t, childDL k s env ts with
      | some a, some b => some (a ++ b)
      | _, _ => none
end

/-- One segment, with a bound on the variable resolutions. -/
def childN : Nat → Seg → Frame S → Option (List (Frame S))
  | 0, _, _ => none
  | n + 1, s, (t, env) => childD (fun m rest => childN n s (m, rest)) s env t

/-- **The children of a frame at a segment.** The bound is the stack length plus one: after the
    first resolution, a guarded body reaches only a variable of an outer binder. -/
def Frame.child (s : Seg) (f : Frame S) : Option (List (Frame S)) :=
  childN (f.2.length + 1) s f

/-- **The terms at a path.** A refusal is `none`. -/
def Term.at (t : Term S.sig) (π : List Seg) : Option (List (Frame S)) :=
  atG Frame.child π [(t, [])]

section Sem
variable (α : Table S) (β : Table S.op)

/-- The codecs of a binder stack. -/
def envSem : List (Term S.sig) → List S.C
  | [] => []
  | m :: ms => denote α β m (envSem ms) :: envSem ms

/-- The codec of a frame: its term over its stack. -/
def Frame.sem (f : Frame S) : S.C := denote α β f.1 (envSem α β f.2)

end Sem


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


/-! ## The frames that a path can reach -/

/-- **One frame reaches another** inside one segment: through a binder, a variable, an option, a
    slot or a position. -/
inductive Reach : Frame S → Frame S → Prop where
  | refl (f : Frame S) : Reach f f
  | mu {b env g} : Reach (b, .mu b :: env) g → Reach (.mu b, env) g
  | var {i env m g} : env[i]? = some m → Reach (m, env.drop (i + 1)) g → Reach (.var i, env) g
  | union {os env o g} : o ∈ os → Reach (o, env) g → Reach (.union os, env) g
  | slot {b env g} (k : String) : Reach ((b.slotAt k).term, env) g → Reach (.object b, env) g
  | pos {pre sp suf env t g} (i : Nat) : listChild pre sp suf i = some t → Reach (t, env) g →
      Reach (.list pre sp suf, env) g

omit [Sem S] in
/-- Reach is transitive. -/
theorem Reach.trans {f g h : Frame S} (h₁ : Reach f g) (h₂ : Reach g h) : Reach f h := by
  induction h₁ with
  | refl => exact h₂
  | mu _ ih => exact .mu (ih h₂)
  | var hm _ ih => exact .var hm (ih h₂)
  | union ho _ ih => exact .union ho (ih h₂)
  | slot k _ ih => exact .slot k (ih h₂)
  | pos i hi _ ih => exact .pos i hi (ih h₂)

mutual
/-- **Every child of one segment is a frame that the frame reaches**, where each resolution of a
    variable gives a frame that the binder reaches. -/
theorem childD_reach {k : Term S.sig → List (Term S.sig) → Option (List (Frame S))} {s : Seg}
    (hk : ∀ m rest gs, k m rest = some gs → ∀ g ∈ gs, Reach (m, rest) g) :
    ∀ (env : List (Term S.sig)) (t : Term S.sig) gs, childD k s env t = some gs →
      ∀ g ∈ gs, Reach (t, env) g
  | env, .never, gs, h, g, hg => by
      simp only [childD, Option.some.injEq] at h; subst h; exact absurd hg (by simp)
  | env, .opaq, gs, h, g, hg => by
      simp only [childD, Option.some.injEq] at h; subst h
      rw [List.mem_singleton.mp hg]; exact .refl _
  | env, .mu b, gs, h, g, hg => .mu (childD_reach hk (.mu b :: env) b gs h g hg)
  | env, .var i, gs, h, g, hg => by
      simp only [childD] at h
      revert h
      match hm : env[i]? with
      | some m => intro h; exact .var hm (hk m _ gs h g hg)
      | none => intro h; simp only [Option.some.injEq] at h; subst h; exact absurd hg (by simp)
  | env, .union os, gs, h, g, hg => by
      obtain ⟨o, ho, hr⟩ := childDL_reach hk env os gs h g hg
      exact .union ho hr
  | env, .object b, gs, h, g, hg => by
      cases s with
      | name n =>
        simp only [childD, Option.some.injEq] at h; subst h
        rw [List.mem_singleton.mp hg]; exact .slot n (.refl _)
      | pos i =>
        simp only [childD] at h
        split at h
        · simp only [Option.some.injEq] at h; subst h; exact absurd hg (by simp)
        · exact nomatch h
  | env, .list pre sp suf, gs, h, g, hg => by
      cases s with
      | pos i =>
        simp only [childD, Option.map_eq_some_iff] at h
        obtain ⟨t, ht, rfl⟩ := h
        rw [List.mem_singleton.mp hg]; exact .pos i ht (.refl _)
      | name n =>
        simp only [childD] at h
        split at h
        · simp only [Option.some.injEq] at h; subst h; exact absurd hg (by simp)
        · exact nomatch h
  | env, .prim _, gs, h, g, hg | env, .set _, gs, h, g, hg | env, .held _ _ _ _ _, gs, h, g, hg
  | env, .refine _ _ _, gs, h, g, hg | env, .legacy _ _, gs, h, g, hg => by
      simp only [childD] at h
      split at h
      · simp only [Option.some.injEq] at h; subst h; exact absurd hg (by simp)
      · exact nomatch h
/-- …and every child of the options of a union is a frame that one option reaches. -/
theorem childDL_reach {k : Term S.sig → List (Term S.sig) → Option (List (Frame S))} {s : Seg}
    (hk : ∀ m rest gs, k m rest = some gs → ∀ g ∈ gs, Reach (m, rest) g) :
    ∀ (env : List (Term S.sig)) (os : List (Term S.sig)) gs, childDL k s env os = some gs →
      ∀ g ∈ gs, ∃ o ∈ os, Reach (o, env) g
  | env, [], gs, h, g, hg => by
      simp only [childDL, Option.some.injEq] at h; subst h; exact absurd hg (by simp)
  | env, o :: os, gs, h, g, hg => by
      simp only [childDL] at h
      split at h
      · next a b ha hb =>
        simp only [Option.some.injEq] at h; subst h
        rcases List.mem_append.mp hg with hg' | hg'
        · exact ⟨o, List.mem_cons_self, childD_reach hk env o a ha g hg'⟩
        · obtain ⟨o', ho', hr⟩ := childDL_reach hk env os b hb g hg'
          exact ⟨o', List.mem_cons_of_mem _ ho', hr⟩
      · exact nomatch h
end

/-- Every child of a frame is a frame that the frame reaches. -/
theorem childN_reach : ∀ (n : Nat) (s : Seg) (f : Frame S) gs, childN n s f = some gs →
    ∀ g ∈ gs, Reach f g
  | 0, _, _, _, h, _, _ => nomatch h
  | n + 1, s, (t, env), gs, h, g, hg =>
      childD_reach (fun m rest gs' h' => childN_reach n s (m, rest) gs' h') env t gs h g hg

/-! ## The meaning of a frame -/

section Sem
variable (α : Table S) (β : Table S.op)

/-- **Every frame that a path can reach holds a lawful codec and a guarded term.** -/
def LawfulReach (f : Frame S) : Prop :=
  ∀ g, Reach f g → Lawful Mean.mem (Frame.sem α β g) ∧ g.1.guarded = true

/-- The law of a frame at a segment, with a bound on the variable resolutions. -/
abbrev StepLawN (n : Nat) (f : Frame S) (s : Seg) : Prop :=
  StepLaw (Frame.sem α β) (fun c A => (c.p A).isSome = true) (childN n) getSeg putSeg f s

variable {α β}

/-- A frame that a lawful frame reaches reaches only lawful frames. -/
theorem LawfulReach.of_reach {f g : Frame S} (h : LawfulReach α β f) (hr : Reach f g) :
    LawfulReach α β g :=
  fun g' hr' => h g' (hr.trans hr')

/-- A stack holds one codec per binder. -/
theorem envSem_length : ∀ env : List (Term S.sig), (envSem α β env).length = env.length
  | [] => rfl
  | _ :: env => by simp only [envSem, List.length_cons, envSem_length env]

/-- A variable that the stack binds reads its binder over the entries after the binder. -/
theorem envAt_envSem : ∀ (env : List (Term S.sig)) (i : Nat) (m : Term S.sig), env[i]? = some m →
    envAt (envSem α β env) i = denote α β m (envSem α β (env.drop (i + 1)))
  | [], _, _, h => nomatch h
  | m' :: env, 0, m, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h; rfl
  | _ :: env, i + 1, m, h => by
      simp only [List.getElem?_cons_succ] at h
      simp only [envAt, envSem, List.getD_cons_succ, List.drop_succ_cons]
      exact envAt_envSem env i m h

/-- A variable that the stack does not bind reads nothing. -/
theorem envAt_envSem_none {env : List (Term S.sig)} {i : Nat} (h : env[i]? = none) :
    envAt (envSem α β env) i = .empty := by
  simp only [envAt]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
    rw [envSem_length]; exact List.getElem?_eq_none_iff.mp h)]
  rfl

/-- **A guarded binder reads what its body reads over the binder**, at each orientation. -/
theorem sem_mu {b : Term S.sig} (hg : (Term.mu b).guarded = true) (env : List (Term S.sig))
    (o : Orient) (x : S.V) :
    (Frame.sem α β (.mu b, env)).f o x = (Frame.sem α β (b, .mu b :: env)).f o x :=
  muCodec_fix Mean.d_pos (contractive_body hg (envSem α β env)) o x

end Sem

section Apart
variable {α : Table S} {β : Table S.op}

mutual
/-- **A term that stores one member stores it under every stack.** A variable stores no member
    in the syntax, so no entry of the stack decides the member. -/
theorem denote_μ_of_μSyn : ∀ (t : Term S.sig) {m : S.M} (ρ : List S.C), μSyn (S := S) t = some m →
    (denote α β t ρ).μ = some m
  | .prim _, _, _, h => h
  | .set t, m, ρ, h => by
      simp only [μSyn] at h
      simp only [denote, denoteAbs]
      revert h
      cases Mean.set (B := S.sig) with
      | none => intro h; exact nomatch h
      | some L =>
        intro h
        obtain ⟨m', hm', h'⟩ := Option.bind_eq_some_iff.mp h
        rw [L.lift_μ]
        exact (denote_μ_of_μSyn t ρ hm').symm ▸ h'
  | .list _ _ _, m, ρ, h => by
      simp only [μSyn] at h
      simp only [denote, denoteAbs]
      revert h
      cases Mean.list (B := S.sig) with
      | none => intro h; exact nomatch h
      | some L => intro h; exact h
  | .held _ t _ _ _, _, ρ, h => denote_μ_of_μSyn t ρ h
  | .refine t _ _, _, ρ, h => denote_μ_of_μSyn t ρ h
  | .legacy t _, _, ρ, h => denote_μ_of_μSyn t ρ h
  | .object (.mk _ _ _), m, ρ, h => by
      simp only [μSyn] at h
      simp only [denote, denoteAbs, bodySemAbs]
      revert h
      cases Mean.map (B := S.sig) with
      | none => intro h; exact nomatch h
      | some F => intro h; exact h
  | .union os, m, ρ, h => by
      simp only [μSyn] at h
      simp only [denote, denoteAbs]
      show unanimous (denoteμs α β os ρ) = some m
      rw [denoteμs_of_μSyn os ρ (unanimous_spec h)]
      exact h
  | .opaq, _, _, h | .never, _, _, h | .var _, _, _, h | .mu _, _, _, h => nomatch h
/-- …and the members of the options of such a union. -/
theorem denoteμs_of_μSyn : ∀ (os : List (Term S.sig)) {m : S.M} (ρ : List S.C),
    (∀ x ∈ μSynList (S := S) os, x = some m) → denoteμs α β os ρ = μSynList (S := S) os
  | [], _, _, _ => rfl
  | o :: os, m, ρ, h => by
      simp only [μSynList, List.mem_cons, forall_eq_or_imp] at h
      show (denote α β o ρ).μ :: denoteμs α β os ρ = μSyn o :: μSynList os
      rw [denote_μ_of_μSyn o ρ h.1, h.1, denoteμs_of_μSyn os ρ h.2]
end

/-- **The store refuses a segment apart from the term.** Where a lawful frame reads an attribute,
    the attribute carries the member of the term, and no container of the segment carries that
    member. -/
theorem apart_refuses {f : Frame S} {s : Seg} (hl : Lawful Mean.mem (Frame.sem α β f))
    (hap : apartAt S s f.1 = true) {A : S.V} (hA : ((Frame.sem α β f).p A).isSome = true) :
    getSeg s A = none ∧ ∀ B, putSeg s B A = none := by
  unfold apartAt at hap
  revert hap
  match hμ : μSyn (S := S) f.1 with
  | none => intro hap; exact nomatch hap
  | some m =>
    intro hap
    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hap
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hA
    have hmem : Mean.mem A = m := hl.reads (denote_μ_of_μSyn f.1 _ hμ) hv
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

end Apart

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

/-- **The term of a name reads what the entry codec of the name reads.** A closed body gives an
    undeclared name `never`, and no entry codec: each reads nothing. -/
theorem slotAt_term_p (τ : (s : Bool) → TableAt S.sig s) (fields : Finset String)
    (f : {k // k ∈ fields} → ObjectSlot S.sig) (wild : Option (Term S.sig)) (k : String)
    (ρ : List S.C) (x : S.V) :
    (denoteAbs τ ((Body.mk fields f wild).slotAt k).term ρ).p x =
      (entryCodec ⟨fields, fun k => fieldSemAbs τ (f k) ρ⟩ (rcOf (wildSemAbs τ wild ρ)) k).bind
        (·.p x) := by
  rcases Decidable.em (k ∈ fields) with h | h
  · have hat : (⟨fields, fun k => fieldSemAbs τ (f k) ρ⟩ : MapOf _).at k =
        some (fieldSemAbs τ (f ⟨k, h⟩) ρ) :=
      MapOf.at_of_mem (m := ⟨fields, fun k => fieldSemAbs τ (f k) ρ⟩) ⟨k, h⟩
    rw [Body.slotAt_pos (b := Body.mk fields f wild) h, entryCodec, hat, Option.bind_some]
    show (denoteAbs τ (f ⟨k, h⟩).term ρ).p x = _
    cases f ⟨k, h⟩ <;> rfl
  · have hat : (⟨fields, fun k => fieldSemAbs τ (f k) ρ⟩ : MapOf _).at k = none :=
      MapOf.at_none (m := ⟨fields, fun k => fieldSemAbs τ (f k) ρ⟩) h
    rw [Body.slotAt_neg (b := Body.mk fields f wild) h, entryCodec, hat]
    cases wild <;> rfl

/-! ## The step laws -/

section Rows
variable (α : Table S) (β : Table S.op)

/-- **The object row of the strong law.** A frame at an object keeps its law at every name: the
    child is the term of the slot over the same stack. -/
theorem object_stepLaw (n : Nat) (b : Body S.sig) (env : List (Term S.sig)) (k : String) :
    StepLawN α β (n + 1) (.object b, env) (.name k) := by
  intro gs hgs A hA
  have hgs' : gs = [((b.slotAt k).term, env)] := by
    simp only [childN, childD, Option.some.injEq] at hgs
    exact hgs.symm
  subst hgs'
  obtain ⟨fields, f, wild⟩ := b
  refine Or.inr ⟨_, List.mem_singleton_self _, ?_, ?_⟩
  · intro B hB
    simp only [Frame.sem, denote, denoteAbs, bodySemAbs] at hA ⊢
    simp only [getSeg] at hB
    revert hA hB
    rcases hF : (Mean.map (B := S.sig)) with _ | F
    · intro _ hB; exact nomatch hB
    · intro hA hB
      rw [slotAt_term_p]
      exact object_get hA hB
  · intro B A' hput hB
    simp only [Frame.sem, denote, denoteAbs, bodySemAbs] at hA hB ⊢
    simp only [putSeg] at hput
    rw [slotAt_term_p] at hB
    revert hA hput
    rcases hF : (Mean.map (B := S.sig)) with _ | F
    · intro _ hput; exact nomatch hput
    · intro hA hput
      exact object_put hA hput hB

/-- Each option of a union gives its children to the union. -/
theorem childDL_sub {k : Term S.sig → List (Term S.sig) → Option (List (Frame S))} {s : Seg}
    {env : List (Term S.sig)} :
    ∀ {os : List (Term S.sig)} {gs}, childDL k s env os = some gs →
      ∀ o ∈ os, ∃ go, childD k s env o = some go ∧ ∀ g ∈ go, g ∈ gs
  | [], _, _, o, ho => absurd ho (by simp)
  | o₀ :: os, gs, h, o, ho => by
      simp only [childDL] at h
      split at h
      · next a b ha hb =>
        cases h
        rcases List.mem_cons.mp ho with rfl | ho'
        · exact ⟨a, ha, fun g hg => List.mem_append_left _ hg⟩
        · obtain ⟨go, hgo, hsub⟩ := childDL_sub hb o ho'
          exact ⟨go, hgo, fun g hg => List.mem_append_right _ (hsub g hg)⟩
      · exact nomatch h

/-- **The union row of the strong law.** Where each option keeps its law, the union keeps the
    law: the option that reads the attribute is responsible, and its children are children of the
    union. -/
theorem union_stepLaw (n : Nat) (os : List (Term S.sig)) (env : List (Term S.sig)) (s : Seg)
    (hos : ∀ o ∈ os, StepLawN α β (n + 1) (o, env) s) :
    StepLawN α β (n + 1) (.union os, env) s := by
  intro gs hgs A hA
  simp only [childN, childD] at hgs
  have hsel : ∀ X, (Frame.sem α β (.union os, env)).p X =
      select ((denoteList α β os (envSem α β env))) (fun c => c.p) X := fun _ => rfl
  rw [hsel, denoteList_eq] at hA
  obtain ⟨c, hc, hcA⟩ := (select_isSome_attempt _ _ _).mp hA
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hc
  obtain ⟨go, hgo, hsub⟩ := childDL_sub hgs o ho
  rcases hos o ho go hgo A hcA with hr | ⟨g, hg, hget, hput⟩
  · exact Or.inl hr
  · refine Or.inr ⟨g, hsub g hg, hget, fun B A' hB hgB => ?_⟩
    show ((Frame.sem α β (.union os, env)).p A').isSome = true
    rw [hsel, denoteList_eq]
    exact (select_isSome_attempt _ _ _).mpr ⟨_, List.mem_map_of_mem ho, hput B A' hB hgB⟩

/-- **The opaque row of the strong law**: the child is opaque, and the identity reads every
    attribute. -/
theorem opaq_stepLaw (n : Nat) (env : List (Term S.sig)) (s : Seg) :
    StepLawN α β (n + 1) (.opaq, env) s := by
  intro gs hgs A _
  simp only [childN, childD, Option.some.injEq] at hgs
  subst hgs
  exact Or.inr ⟨_, List.mem_singleton_self _, fun _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- **The bottom row of the strong law**: the bottom reads no attribute. -/
theorem never_stepLaw (n : Nat) (env : List (Term S.sig)) (s : Seg) :
    StepLawN α β (n + 1) (.never, env) s := by
  intro _ _ A hA
  exact absurd hA (by simp [Frame.sem, denoteAbs, Codec.empty])

/-- **The row of a term that the store refuses at the segment.** The child is a refusal, or the
    term is apart from the segment and its lawful codec reads no attribute that the store accepts
    there. -/
theorem apart_stepLaw {n : Nat} {f : Frame S} {s : Seg}
    (hc : childN (n + 1) s f = if apartAt S s f.1 then some [] else none)
    (hl : Lawful Mean.mem (Frame.sem α β f)) : StepLawN α β (n + 1) f s := by
  intro gs hgs A hA
  rw [hc] at hgs
  split at hgs
  · next hap => exact Or.inl (apart_refuses hl hap hA)
  · exact nomatch hgs

/-- **The primitive row of the strong law.** A primitive codec is lawful, so a primitive apart
    from the segment reads no attribute that the store accepts there. -/
theorem prim_stepLaw (n : Nat) (g : S.Ground) (env : List (Term S.sig)) (s : Seg) :
    StepLawN α β (n + 1) (.prim g, env) s :=
  apart_stepLaw α β rfl (Mean.lawful_ground g)

/-- **The set row of the strong law.** A lawful set apart from the segment reads no attribute that
    the store accepts there. -/
theorem set_stepLaw (n : Nat) (t : Term S.sig) (env : List (Term S.sig)) (s : Seg)
    (hl : Lawful Mean.mem (Frame.sem α β (.set t, env))) :
    StepLawN α β (n + 1) (.set t, env) s :=
  apart_stepLaw α β rfl hl

/-- **The binder row of the strong law.** A guarded binder reads what its body reads over the
    binder, and its children are the children of the body. -/
theorem mu_stepLaw (n : Nat) (b : Term S.sig) (env : List (Term S.sig)) (s : Seg)
    (hg : (Term.mu b).guarded = true) (h : StepLawN α β (n + 1) (b, .mu b :: env) s) :
    StepLawN α β (n + 1) (.mu b, env) s := by
  have hp : ∀ X, (Frame.sem α β (.mu b, env)).p X = (Frame.sem α β (b, .mu b :: env)).p X :=
    fun X => sem_mu hg env Orient.dual X
  intro gs hgs A hA
  replace hA : ((Frame.sem α β (.mu b, env)).p A).isSome = true := hA
  rw [hp] at hA
  rcases h gs hgs A hA with hr | ⟨g, hg', hget, hput⟩
  · exact Or.inl hr
  · exact Or.inr ⟨g, hg', hget, fun B A' hB hgB => by
      show ((Frame.sem α β (.mu b, env)).p A').isSome = true
      rw [hp]; exact hput B A' hB hgB⟩

/-- **The variable row of the strong law.** A bound variable is its binder over the entries after
    the binder, one resolution down. -/
theorem var_stepLaw (n : Nat) (i : Nat) (env : List (Term S.sig)) (m : Term S.sig) (s : Seg)
    (hm : env[i]? = some m) (h : StepLawN α β n (m, env.drop (i + 1)) s) :
    StepLawN α β (n + 1) (.var i, env) s := by
  have hsem : Frame.sem α β (.var i, env) = Frame.sem α β (m, env.drop (i + 1)) :=
    envAt_envSem env i m hm
  intro gs hgs A hA
  simp only [childN, childD, hm] at hgs
  rw [hsem] at hA ⊢
  exact h gs hgs A hA

/-- …and a free variable reads no attribute. -/
theorem var_none_stepLaw (n : Nat) (i : Nat) (env : List (Term S.sig)) (s : Seg)
    (hm : env[i]? = none) : StepLawN α β (n + 1) (.var i, env) s := by
  intro _ _ A hA
  have hsem : Frame.sem α β (.var i, env) = .empty := envAt_envSem_none hm
  rw [hsem] at hA
  exact absurd hA (by simp [Codec.empty])

end Rows

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

variable {S : Syn} [Sem S]

/-- **The codec of a position is the denotation of the term at the position.** -/
theorem slotsL_listChild {pre : List (Term S.sig)} {sp : Option (Term S.sig)}
    {suf : List (Term S.sig)} (d : Term S.sig → S.C) {i : Nat} {t : Term S.sig} {n : Nat}
    {ds : List S.C} (ht : listChild pre sp suf i = some t)
    (hs : slotsL (pre.map d) (sp.map d) (suf.map d) n = some ds) (hi : i < n) :
    ds[i]? = some (d t) := by
  unfold listChild at ht
  split at ht
  · next t' _ _ hp =>
    cases ht
    obtain ⟨dsF, hF, rfl, hlen, -⟩ := slotsL_split _ _ _ n ds hs
    have hle := slots_le_length _ _ _ _ hF
    have hip : i < (pre.map d).length := by
      rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp hp).1
    have hiF : i < n - (List.map d _).length := lt_of_lt_of_le hip hle
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

section ListRow
variable (α : Table S) (β : Table S.op)

/-- The codec of a frame at a list is the list codec of the terms of the shape over the stack. -/
theorem sem_list {pre : List (Term S.sig)} {sp : Option (Term S.sig)} {suf : List (Term S.sig)}
    {env : List (Term S.sig)} {L : ListA S.V S.M Mean.mem Mean.d}
    (hL : Mean.list (B := S.sig) = some L) :
    Frame.sem α β (.list pre sp suf, env) = listCodec L.toSummand
      (pre.map fun t => denote α β t (envSem α β env))
      (sp.map fun t => denote α β t (envSem α β env))
      (suf.map fun t => denote α β t (envSem α β env)) := by
  simp only [Frame.sem, denote, denoteAbs, hL]
  rw [← denoteList_eq, ← denoteList_eq, ← denoteOpt_eq]

/-- **The list row of the strong law.** A frame at a list keeps its law at every position that
    the shape gives a term: the child reads the entry, and a value that the child reads keeps the
    list readable where the store puts the value in place or appends the value past the end. -/
theorem list_stepLaw (n : Nat) (pre : List (Term S.sig)) (sp : Option (Term S.sig))
    (suf : List (Term S.sig)) (env : List (Term S.sig)) (i : Nat) :
    StepLawN α β (n + 1) (.list pre sp suf, env) (.pos i) := by
  intro gs hgs A hA
  simp only [childN, childD, Option.map_eq_some_iff] at hgs
  obtain ⟨t, ht, rfl⟩ := hgs
  let d : Term S.sig → S.C := fun t => denote α β t (envSem α β env)
  replace hA : ((Frame.sem α β (.list pre sp suf, env)).p A).isSome = true := hA
  rcases hL : (Mean.list (B := S.sig)) with _ | L
  · simp only [Frame.sem, denote, denoteAbs, hL] at hA
    exact absurd hA (by simp [Codec.empty])
  rw [sem_list α β hL] at hA
  obtain ⟨xs, ds, hxs, hds, hall⟩ := listCodec_p_isSome.mp hA
  have hlen := slotsL_length _ _ _ _ _ hds
  refine Or.inr ⟨(t, env), List.mem_singleton_self _, ?_, ?_⟩
  · intro B hB
    show ((d t).p B).isSome = true
    simp only [getSeg, hL, hxs, Option.bind_some] at hB
    have hi : i < xs.length := (List.getElem?_eq_some_iff.mp hB).1
    have hdi := slotsL_listChild d ht hds hi
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
    replace hB : ((d t).p B).isSome = true := hB
    show ((Frame.sem α β (.list pre sp suf, env)).p A').isSome = true
    rw [sem_list α β hL]
    simp only [putSeg, hL, hxs, Option.map_some, Option.some.injEq] at hput
    subst hput
    refine listCodec_p_isSome.mpr ?_
    rcases Nat.lt_or_ge i xs.length with hi | hi
    · rw [if_pos hi]
      refine ⟨_, ds, L.p.out_into _, by rw [List.length_set]; exact hds, fun q hq => ?_⟩
      rcases mem_zip_set ds xs i B q hq with hq' | ⟨hq1, hq2⟩
      · exact hall q hq'
      · rw [slotsL_listChild d ht hds hi, Option.some.injEq] at hq1
        rw [← hq1, hq2]; exact hB
    · rw [if_neg (Nat.not_lt.mpr hi)]
      obtain ⟨dsF, hF, -, -, -⟩ := slotsL_split _ _ _ _ ds hds
      have hle := slots_le_length _ _ _ _ hF
      simp only [List.length_map] at hle
      unfold listChild at ht
      split at ht
      · next hp =>
        exact absurd (List.getElem?_eq_some_iff.mp hp).1 (by omega)
      · next hp =>
        cases ht
        simp only [Option.map_some, List.map_nil, slotsL_nil_suf] at hds ⊢
        refine ⟨_, ds ++ [d t], L.p.out_into _, ?_, fun q hq => ?_⟩
        · rw [List.length_append, List.length_singleton]; exact slots_snoc _ _ _ _ hds
        · rw [List.zip_append (by omega)] at hq
          rcases List.mem_append.mp hq with hq' | hq'
          · exact hall q hq'
          · rw [List.zip_cons_cons, List.zip_nil_left, List.mem_singleton] at hq'
            subst hq'; exact hB
      · cases ht
        exact absurd hB (by simp [d, denoteAbs, Codec.empty])
      · exact nomatch ht

end ListRow

/-! ## The strong law at a term -/

section Main
variable (α : Table S) (β : Table S.op)

/-- **Every frame that reaches only lawful codecs and guarded terms keeps its law** at each
    segment, under every bound on the variable resolutions. -/
theorem stepLawN_of_reach : ∀ (n : Nat) (f : Frame S) (s : Seg), LawfulReach α β f →
    StepLawN α β n f s := by
  intro n
  induction n with
  | zero => intro _ _ _ _ hgs; exact nomatch hgs
  | succ n ihn =>
    suffices h : ∀ d (t : Term S.sig) env s, t.depth < d → LawfulReach α β (t, env) →
        StepLawN α β (n + 1) (t, env) s from
      fun f s hR => h _ f.1 f.2 s (Nat.lt_succ_self _) hR
    intro d
    induction d with
    | zero => intro _ _ _ hd; exact absurd hd (Nat.not_lt_zero _)
    | succ d ihd =>
      intro t env s hd hR
      have hl := fun g hg => (hR g hg).1
      match t, s with
      | .never, s => exact never_stepLaw α β n env s
      | .opaq, s => exact opaq_stepLaw α β n env s
      | .prim g, s => exact prim_stepLaw α β n g env s
      | .set t', s => exact set_stepLaw α β n t' env s (hl _ (.refl _))
      | .held _ _ _ _ _, s | .refine _ _ _, s | .legacy _ _, s =>
        exact apart_stepLaw α β rfl (hl _ (.refl _))
      | .object b, .name k => exact object_stepLaw α β n b env k
      | .object _, .pos _ => exact apart_stepLaw α β rfl (hl _ (.refl _))
      | .list pre sp suf, .pos i => exact list_stepLaw α β n pre sp suf env i
      | .list _ _ _, .name _ => exact apart_stepLaw α β rfl (hl _ (.refl _))
      | .union os, s =>
        exact union_stepLaw α β n os env s fun o ho =>
          ihd o env s
            (by have := Term.depth_le_depthL ho; simp only [Term.depth] at hd; omega)
            (hR.of_reach (.union ho (.refl _)))
      | .mu b, s =>
        exact mu_stepLaw α β n b env s (hR _ (.refl _)).2
          (ihd b _ s (by simp only [Term.depth] at hd; omega) (hR.of_reach (.mu (.refl _))))
      | .var i, s =>
        match hm : env[i]? with
        | some m => exact var_stepLaw α β n i env m s hm (ihn _ s (hR.of_reach (.var hm (.refl _))))
        | none => exact var_none_stepLaw α β n i env s hm

/-- **The law of a frame at a segment**, at the bound of `Frame.child`. -/
theorem stepLaw_of_reach (f : Frame S) (s : Seg) (hR : LawfulReach α β f) :
    StepLaw (Frame.sem α β) (fun c A => (c.p A).isSome = true) Frame.child getSeg putSeg f s :=
  stepLawN_of_reach α β (f.2.length + 1) f s hR

end Main

/-! ## The frames of a typed term -/

section Approx
variable {V M : Type} {member : V → M} {depth : V → Nat}

/-- **A codec that lawful codecs approximate at every depth is lawful**, where each approximant
    keeps the member of the codec. -/
theorem lawful_of_approx {c : Codec V M}
    (h : ∀ d, ∃ c', Lawful member c' ∧ AgreeLe depth d c c' ∧ ∀ m, c.μ = some m → c'.μ = some m) :
    Lawful member c where
  inv {o x y} hxy := by
    obtain ⟨c', hl, ha, -⟩ := h (max (depth x) (depth y))
    rw [ha.f o x (Nat.le_max_left _ _)] at hxy
    rw [ha.f o.op y (Nat.le_max_right _ _)]
    exact hl.inv hxy
  writes {m} hm {t a} he := by
    obtain ⟨c', hl, ha, hμ⟩ := h (depth t)
    have he' : c'.e t = some a := (ha.f Orient.host t le_rfl).symm.trans he
    exact hl.writes (hμ m hm) he'

end Approx

section Discharge
variable {α : Table S} {β : Table S.op}

mutual
/-- **Over a stack of codecs that store no member, a term stores its syntactic member.** -/
theorem denote_μ_eq : ∀ (t : Term S.sig) (ρ : List S.C), (∀ i, (envAt ρ i).μ = none) →
    (denote α β t ρ).μ = μSyn (S := S) t
  | .prim _, _, _ => rfl
  | .set t, ρ, h => by
      simp only [denote, denoteAbs, μSyn]
      cases Mean.set (B := S.sig) with
      | none => rfl
      | some L => rw [L.lift_μ]; exact congrArg (·.bind L.member) (denote_μ_eq t ρ h)
  | .list _ _ _, _, _ => by
      simp only [denote, denoteAbs, μSyn]
      cases Mean.list (B := S.sig) <;> rfl
  | .held _ t _ _ _, ρ, h => denote_μ_eq t ρ h
  | .refine t _ _, ρ, h => denote_μ_eq t ρ h
  | .legacy t _, ρ, h => denote_μ_eq t ρ h
  | .opaq, _, _ | .never, _, _ | .mu _, _, _ => rfl
  | .var i, _, h => h i
  | .object (.mk _ _ _), _, _ => by
      simp only [denote, denoteAbs, bodySemAbs, μSyn]
      cases Mean.map (B := S.sig) <;> rfl
  | .union os, ρ, h => congrArg unanimous (denoteμs_eq os ρ h)
/-- …and the members of the options. -/
theorem denoteμs_eq : ∀ (os : List (Term S.sig)) (ρ : List S.C), (∀ i, (envAt ρ i).μ = none) →
    denoteμs α β os ρ = μSynList (S := S) os
  | [], _, _ => rfl
  | o :: os, ρ, h => by
      show (denote α β o ρ).μ :: denoteμs α β os ρ = μSyn o :: μSynList os
      rw [denote_μ_eq o ρ h, denoteμs_eq os ρ h]
end


variable (α β) in
/-- **The approximant of a binder stack**: each binder at the stage `n` of its body, over the
    approximants of the entries after the binder. -/
def approxEnv (n : Nat) : List (Term S.sig) → List S.C
  | [] => []
  | m :: ms =>
      (match m with
        | .mu b => muStage (fun c => denote α β b (c :: approxEnv n ms)) n
        | m => denote α β m (approxEnv n ms)) :: approxEnv n ms

variable (α β) in
/-- **The premises of one frame**: a typed and guarded term, whose stack variables sit under no
    `held`, and whose obligations hold over every approximant of its stack. -/
def FrameObl (t : Term S.sig) (env : List (Term S.sig)) : Prop :=
  (∃ T μ, Typed α β t T μ) ∧ t.guarded = true ∧ (∀ i < env.length, Term.use i t ≤ 2) ∧
    ∀ n, Obligations α β t (approxEnv α β n env)

variable (α β) in
/-- The premises of a binder stack: each entry is a binder whose frame holds its premises. -/
def EnvObl : List (Term S.sig) → Prop
  | [] => True
  | m :: ms => (∃ b, m = .mu b) ∧ FrameObl α β m ms ∧ EnvObl ms

/-- An approximant holds one codec per binder. -/
theorem approxEnv_length (n : Nat) : ∀ env : List (Term S.sig),
    (approxEnv α β n env).length = env.length
  | [] => rfl
  | _ :: env => by simp only [approxEnv, List.length_cons, approxEnv_length n env]

/-- A variable past the stack reads the bottom. -/
theorem envAt_of_length_le {ρ : List S.C} {i : Nat} (h : ρ.length ≤ i) : envAt ρ i = .empty := by
  simp only [envAt]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

/-- Each stage of a binder whose premises hold is lawful, over a lawful stack. -/
theorem lawful_stage {b : Term S.sig} {ρ : List S.C} (hty : ∃ T μ, Typed α β (.mu b) T μ)
    (hob : Obligations α β (.mu b) ρ) (henv : ∀ i, Lawful Mean.mem (envAt ρ i)) :
    ∀ k, Lawful Mean.mem (muStage (fun c => denote α β b (c :: ρ)) k) := by
  obtain ⟨T, μ, hty⟩ := hty
  cases hty with
  | mu _ hb =>
    intro k
    induction k with
    | zero => exact Lawful.empty
    | succ k ih =>
      exact soundnessIn (_ :: ρ) hb (hob k ih) fun i => match i with
        | 0 => ih
        | i + 1 => henv i

/-- The approximant of a stack whose premises hold is lawful. -/
theorem envObl_lawful (n : Nat) : ∀ env : List (Term S.sig), EnvObl α β env →
    ∀ i, Lawful Mean.mem (envAt (approxEnv α β n env) i)
  | [], _, i => by simp only [approxEnv, envAt, List.getD_nil]; exact Lawful.empty
  | m :: ms, ⟨⟨b, hb⟩, hm, hms⟩, i => by
      subst hb
      match i with
      | 0 => exact lawful_stage hm.1 (hm.2.2.2 n) (envObl_lawful n ms hms) n
      | i + 1 => exact envObl_lawful n ms hms i

/-- A binder that the stack holds keeps its premises. -/
theorem envObl_get : ∀ (env : List (Term S.sig)) (i : Nat) (m : Term S.sig), EnvObl α β env →
    env[i]? = some m →
      (∃ b, m = .mu b) ∧ FrameObl α β m (env.drop (i + 1)) ∧ EnvObl α β (env.drop (i + 1))
  | [], _, _, _, h => nomatch h
  | _ :: ms, 0, m, ⟨hb, hm, hms⟩, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h; exact ⟨hb, hm, hms⟩
  | _ :: ms, i + 1, m, ⟨_, _, hms⟩, h => by
      simp only [List.getElem?_cons_succ] at h
      exact envObl_get ms i m hms h

/-- **The stack of limits agrees with each approximant at or above a depth.** -/
theorem envSem_agree (d n : Nat) (hdn : d ≤ n) : ∀ env : List (Term S.sig), EnvObl α β env →
    ∀ i, AgreeLe (Mean.d (B := S.sig)) d (envAt (envSem α β env) i)
      (envAt (approxEnv α β n env) i)
  | [], _, i => by simp only [envSem, approxEnv]; exact AgreeLe.refl _ _
  | m :: ms, ⟨⟨b, hb⟩, hm, hms⟩, i => by
      subst hb
      have ih := envSem_agree d n hdn ms hms
      match i with
      | 0 =>
        obtain ⟨-, hg, huse, -⟩ := hm
        have hg' := hg
        simp only [Term.guarded, Bool.and_eq_true, decide_eq_true_eq] at hg'
        have hstage : ∀ k, AgreeLe (Mean.d (B := S.sig)) d
            (muStage (fun c => denote α β b (c :: envSem α β ms)) k)
            (muStage (fun c => denote α β b (c :: approxEnv α β n ms)) k) := by
          intro k
          induction k with
          | zero => exact AgreeLe.refl _ _
          | succ k ihk =>
            refine denote_agree b hg'.2 d _ _ fun j => ?_
            match j with
            | 0 => exact UseAgree.mono (u' := 2) ihk (by omega)
            | j + 1 =>
              rcases Nat.lt_or_ge j ms.length with hj | hj
              · exact UseAgree.mono (u' := 2) (ih j) (huse j hj)
              · show UseAgree _ d (envAt (envSem α β ms) j) (envAt (approxEnv α β n ms) j)
                rw [envAt_of_length_le (by rw [envSem_length]; exact hj),
                  envAt_of_length_le (by rw [approxEnv_length]; exact hj)]
                exact UseAgree.refl _ _ _
        exact ((muCodec_agree Mean.d_pos (contractive_body hg (envSem α β ms)) n).mono hdn).trans
          (hstage n)
      | i + 1 => exact ih i

/-- **A frame whose premises hold is lawful**: lawful approximants agree with it at every depth,
    and each approximant keeps its member. -/
theorem frameObl_lawful {t : Term S.sig} {env : List (Term S.sig)} (h : FrameObl α β t env)
    (henv : EnvObl α β env) : Lawful Mean.mem (Frame.sem α β (t, env)) := by
  obtain ⟨⟨T, μ, hty⟩, hg, huse, hob⟩ := h
  have hμ : (Frame.sem α β (t, env)).μ = μSyn (S := S) t := by
    refine denote_μ_eq t _ fun i => ?_
    rcases Nat.lt_or_ge i env.length with hi | hi
    · have hm := List.getElem?_eq_getElem hi
      obtain ⟨⟨b, hb⟩, -⟩ := envObl_get env i _ henv hm
      rw [hb] at hm
      rw [envAt_envSem env i _ hm]; rfl
    · rw [envAt_of_length_le (by rw [envSem_length]; exact hi)]; rfl
  refine lawful_of_approx (depth := Mean.d (B := S.sig)) fun d =>
    ⟨denote α β t (approxEnv α β d env),
      soundnessIn _ hty (hob d) (envObl_lawful d env henv),
      denote_agree t hg d _ _ fun i => ?_, fun m hm => ?_⟩
  · rcases Nat.lt_or_ge i env.length with hi | hi
    · exact UseAgree.mono (u' := 2) (envSem_agree d d le_rfl env henv i) (huse i hi)
    · rw [envAt_of_length_le (by rw [envSem_length]; exact hi),
        envAt_of_length_le (by rw [approxEnv_length]; exact hi)]
      exact UseAgree.refl _ _ _
  · rw [hμ] at hm
    exact denote_μ_of_μSyn t _ hm


omit [Sem S] in
/-- Each term of a guarded list is guarded. -/
theorem guardedL_mem : ∀ {ts : List (Term S.sig)} {t : Term S.sig}, Term.guardedL ts = true →
    t ∈ ts → t.guarded = true
  | _ :: _, _, h, ht => by
      simp only [Term.guardedL, Bool.and_eq_true] at h
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact h.1
      · exact guardedL_mem h.2 ht'

omit [Sem S] in
/-- A term of a list reads a variable at most as the list does. -/
theorem useL_mem (i : Nat) : ∀ {ts : List (Term S.sig)} {t : Term S.sig}, t ∈ ts →
    Term.use i t ≤ Term.useL i ts
  | _ :: _, _, ht => by
      simp only [Term.useL]
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact Nat.le_max_left _ _
      · exact le_trans (useL_mem i ht') (Nat.le_max_right _ _)

omit [Sem S] in
/-- Where a container reads a variable under no `held`, its elements read the variable under no
    `held`. -/
theorem le_of_useUnder {u : Nat} (h : useUnder u ≤ 2) : u ≤ 2 := by
  unfold useUnder at h; split at h <;> omega

/-- **The body of a binder keeps the premises**: its obligations hold over each stage of the
    binder, and the guard bounds the binder variable. -/
theorem frameObl_mu {b : Term S.sig} {env : List (Term S.sig)} (h : FrameObl α β (.mu b) env)
    (henv : EnvObl α β env) : FrameObl α β b (.mu b :: env) := by
  obtain ⟨hty, hg, huse, hob⟩ := h
  have hg' := hg
  simp only [Term.guarded, Bool.and_eq_true, decide_eq_true_eq] at hg'
  obtain ⟨T, μ, hty'⟩ := hty
  cases hty' with
  | mu _ hb =>
    refine ⟨⟨_, _, hb⟩, hg'.2, fun i hi => ?_, fun n => ?_⟩
    · match i with
      | 0 => omega
      | i + 1 =>
        have := huse i (by simpa using hi)
        simpa only [Term.use] using this
    · exact hob n n (lawful_stage ⟨_, _, .mu hg hb⟩ (hob n) (envObl_lawful n env henv) n)

/-- An option of a union keeps the premises of the union. -/
theorem frameObl_union {os : List (Term S.sig)} {o : Term S.sig} {env : List (Term S.sig)}
    (h : FrameObl α β (.union os) env) (ho : o ∈ os) : FrameObl α β o env := by
  obtain ⟨⟨T, μ, hty⟩, hg, huse, hob⟩ := h
  cases hty with
  | union hl =>
    exact ⟨TypedListμ.forall hl o ho, guardedL_mem hg ho,
      fun i hi => le_trans (useL_mem i ho) (huse i hi),
      fun n => obligationsList_iff.mp (hob n).1 o ho⟩

/-- The term of a name keeps the premises of the object. -/
theorem frameObl_slot {b : Body S.sig} {env : List (Term S.sig)} (k : String)
    (h : FrameObl α β (.object b) env) : FrameObl α β (b.slotAt k).term env := by
  obtain ⟨⟨T, μ, hty⟩, hg, huse, hob⟩ := h
  obtain ⟨fields, f, wild⟩ := b
  simp only [Term.guarded, Body.guarded, Bool.and_eq_true, decide_eq_true_eq] at hg
  have hu : ∀ i < env.length, Body.use i (Body.mk fields f wild) ≤ 2 := fun i hi =>
    le_of_useUnder (by simpa only [Term.use] using huse i hi)
  have hslot : ∀ (sl : ObjectSlot S.sig), ObjectSlot.guarded sl = true →
      (∀ i < env.length, ObjectSlot.use i sl ≤ 2) → (∀ n, ObligationsField α β sl (approxEnv α β n env)) →
      (∃ T μ, Typed α β sl.term T μ) → FrameObl α β sl.term env := by
    intro sl hgs hus hos hts
    cases sl <;> exact ⟨hts, hgs, hus, hos⟩
  cases hty with
  | object hF hf hr =>
    simp only [Body.fields_mk, Body.at_mk, Body.wild_mk] at hf hr
    rcases Decidable.em (k ∈ fields) with hk | hk
    · rw [Body.slotAt_pos (b := Body.mk fields f wild) hk]
      refine hslot _ (hg.1 ⟨k, hk⟩) (fun i hi => le_trans ?_ (hu i hi))
        (fun n => (hob n).1 ⟨k, hk⟩) ?_
      · simp only [Body.use]
        exact le_trans (Finset.le_sup (f := fun k => ObjectSlot.use i (f k))
          (Finset.mem_attach _ ⟨k, hk⟩)) (Nat.le_max_left _ _)
      · obtain ⟨t', ht', hsh⟩ := TypedField.term (hf ⟨k, hk⟩)
        show ∃ T μ, Typed α β (f ⟨k, hk⟩).term T μ
        rcases hsh with he | he <;> (rw [he]; exact ⟨_, _, ht'⟩)
    · rw [Body.slotAt_neg (b := Body.mk fields f wild) hk]
      show FrameObl α β (Body.block (Body.mk fields f wild)) env
      simp only [Body.block, Body.wild_mk]
      cases hr with
      | none => exact ⟨⟨_, _, .never⟩, rfl, fun i _ => by simp [Term.use], fun _ => trivial⟩
      | some ht' =>
        refine ⟨⟨_, _, ht'⟩, hg.2, fun i hi => le_trans ?_ (hu i hi), fun n => (hob n).2⟩
        simp only [Body.use, Term.useO]
        exact Nat.le_max_right _ _

/-- The term of a position keeps the premises of the list. -/
theorem frameObl_pos {pre : List (Term S.sig)} {sp : Option (Term S.sig)}
    {suf : List (Term S.sig)} {env : List (Term S.sig)} {i : Nat} {t : Term S.sig}
    (h : FrameObl α β (.list pre sp suf) env) (ht : listChild pre sp suf i = some t) :
    FrameObl α β t env := by
  obtain ⟨⟨T, μ, hty⟩, hg, huse, hob⟩ := h
  simp only [Term.guarded, Bool.and_eq_true] at hg
  have hu : ∀ j < env.length,
      max (Term.useL j pre) (max (Term.useO j sp) (Term.useL j suf)) ≤ 2 := fun j hj =>
    le_of_useUnder (by simpa only [Term.use] using huse j hj)
  cases hty with
  | list hL hp hs hf =>
    unfold listChild at ht
    split at ht
    · next hpre =>
      cases ht
      have hm : t ∈ pre := List.mem_of_getElem? hpre
      exact ⟨TypedList.forall hp t hm, guardedL_mem hg.1.1 hm,
        fun j hj => le_trans (useL_mem j hm) (le_trans (Nat.le_max_left _ _) (hu j hj)),
        fun n => obligationsList_iff.mp (hob n).1 t hm⟩
    · cases ht
      cases hs with
      | some hts =>
        refine ⟨⟨_, _, hts⟩, hg.1.2, fun j hj => le_trans ?_ (hu j hj), fun n => (hob n).2.1⟩
        simp only [Term.useO]
        exact le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    · cases ht
      exact ⟨⟨_, _, .never⟩, rfl, fun j _ => by simp [Term.use], fun _ => trivial⟩
    · exact nomatch ht

/-- **The premises of a frame reach every frame that it reaches.** -/
theorem reach_obl {f g : Frame S} (hr : Reach f g) :
    FrameObl α β f.1 f.2 → EnvObl α β f.2 → FrameObl α β g.1 g.2 ∧ EnvObl α β g.2 := by
  induction hr with
  | refl => exact fun h he => ⟨h, he⟩
  | mu _ ih => exact fun h he => ih (frameObl_mu h he) ⟨⟨_, rfl⟩, h, he⟩
  | var hm _ ih =>
    exact fun _ he => let ⟨_, h', he'⟩ := envObl_get _ _ _ he hm; ih h' he'
  | union ho _ ih => exact fun h he => ih (frameObl_union h ho) he
  | slot k _ ih => exact fun h he => ih (frameObl_slot k h) he
  | pos i hi _ ih => exact fun h he => ih (frameObl_pos h hi) he

/-- **A typed and guarded term whose obligations hold reaches only lawful codecs and guarded
    terms**, under every binder that a path enters. -/
theorem lawfulReach_of_typed {t : Term S.sig} {T : S.V → Prop} {μ : Option S.M}
    (hty : Typed α β t T μ) (hob : Obligations α β t) (hg : t.guarded = true) :
    LawfulReach α β (t, []) := fun _ hr =>
  let ⟨h, he⟩ := reach_obl hr ⟨⟨T, μ, hty⟩, hg, fun _ hi => absurd hi (Nat.not_lt_zero _),
    fun _ => hob⟩ trivial
  ⟨frameObl_lawful h he, h.2.1⟩

/-- **The strong law.** Take a typed and guarded term whose obligations hold, and a writer that
    agrees with every frame of the frontier at a path. An attribute that the term reads stays
    readable after the store puts, at the path, what the writer wrote. -/
theorem strong_law {t : Term S.sig} {T : S.V → Prop} {μ : Option S.M} (hty : Typed α β t T μ)
    (hob : Obligations α β t) (hg : t.guarded = true) (π : List Seg) (res : List (Frame S))
    (hat : t.at π = some res)
    (w : S.C) (hw : ∀ g ∈ res, ∀ x a, w.e x = some a → ((Frame.sem α β g).p a).isSome)
    {A A' x a : S.V} (hA : ((denote α β t).p A).isSome) (hx : w.e x = some a)
    (hput : putPath π a A = some A') : ((denote α β t).p A').isSome := by
  exact path_law (Frame.sem α β) _ Frame.child getSeg putSeg (LawfulReach α β)
    (stepLaw_of_reach α β)
    (fun f s gs hf hc g hg => hf.of_reach (childN_reach _ s f gs hc g hg))
    π [(t, [])] res hat
    (fun f hf => by rw [List.mem_singleton.mp hf]; exact lawfulReach_of_typed hty hob hg)
    (t, []) (List.mem_singleton_self _) A a A' hA (fun g hg => hw g hg x a hx) hput

end Discharge

/-! ## Narrowing a union by a clause -/

/-- **A clause as the host writes it**: each named key required at a term, and every other name
    open. The clause is an ordinary object term. -/
abbrev clauseTerm {B : Sig} (keys : Finset String) (T : {k // k ∈ keys} → Term B) : Term B :=
  .object (.mk keys (fun k => .req (T k)) (some .opaq))

/-- **Narrowing by a clause**: the options that the disjointness decision does not separate from
    the clause. -/
def narrow {B : Sig} [Leaf B] (φ : Term B) (os : List (Term B)) : List (Term B) :=
  os.filter fun o => !Term.disjoint pair0 φ o

section Narrow
variable {α : Table S} {β : Table S.op}

omit [Sem S] in
/-- An option that narrowing drops is one that the decision separates from the clause. -/
theorem disjoint_of_dropped [Leaf S.sig] {φ o : Term S.sig} {os : List (Term S.sig)} (ho : o ∈ os)
    (hd : o ∉ narrow φ os) : Term.disjoint pair0 φ o = true := by
  unfold narrow at hd
  rw [List.mem_filter] at hd
  cases h : Term.disjoint pair0 φ o
  · exact absurd ⟨ho, by rw [h]; rfl⟩ hd
  · rfl

omit [Sem S] in
/-- A first match over the options that a filter keeps is the first match over all options,
    where each dropped option acts nowhere at the input. -/
theorem select_filter {V M X Y : Type} {run : Codec V M → X → Option Y} {x : X}
    {keep : Term S.sig → Bool} {d : Term S.sig → Codec V M} :
    ∀ os : List (Term S.sig), (∀ o ∈ os, keep o = false → run (d o) x = none) →
      select ((os.filter keep).map d) run x = select (os.map d) run x
  | [], _ => rfl
  | o :: os, h => by
      have ih := select_filter os fun o' ho' => h o' (List.mem_cons_of_mem _ ho')
      rw [List.filter_cons]
      cases hk : keep o
      · simp only [Bool.false_eq_true, if_false, List.map_cons]
        rw [ih]
        simp only [select, List.find?_cons, h o List.mem_cons_self hk, Option.isSome_none]
      · simp only [if_true, List.map_cons]
        simp only [select, List.find?_cons] at ih ⊢
        split
        · rfl
        · exact ih

variable [PrimAdmA S] [Leaf S.sig] [LeafAdmA S] [LeafMeet S.sig] [FormerAdmA S] [Shapes S]
  [TopLaws S]

/-- **Narrowing drops only what the clause excludes**: an option that narrowing drops reads no
    attribute that the stored admission of the clause admits. -/
theorem narrow_drops {φ o : Term S.sig} {os : List (Term S.sig)} (ho : o ∈ os)
    (hd : o ∉ narrow φ os) (ρ : List S.C) {a : S.V} (hφ : AdmA α β φ [] a = true) :
    AdmA α β o ρ a = false := by
  have h := disjoint_soundA (α := α) (β := β) pair0 φ o (disjoint_of_dropped ho hd) [] ρ
    (fun _ _ hp => nomatch hp) a
  rw [hφ, Bool.true_and] at h
  exact h

/-- **Narrowing is the restriction to the clause**: on an attribute that the stored admission of
    the clause admits, the narrowed union reads what the union reads. -/
theorem narrow_reads (φ : Term S.sig) (os : List (Term S.sig)) (ρ : List S.C) {a : S.V}
    (hφ : AdmA α β φ [] a = true) :
    (denote α β (.union (narrow φ os)) ρ).f S.o.op a = (denote α β (.union os) ρ).f S.o.op a := by
  show select (denoteList α β (narrow φ os) ρ) (·.f S.o.op) a =
    select (denoteList α β os ρ) (·.f S.o.op) a
  rw [denoteList_eq, denoteList_eq]
  refine select_filter os fun o ho hk => ?_
  have hd : o ∉ narrow φ os := fun h => by
    unfold narrow at h; rw [List.mem_filter] at h; rw [h.2] at hk; exact nomatch hk
  have h := narrow_drops (α := α) (β := β) ho hd ρ hφ
  rw [AdmA_eq_isSome] at h
  exact Option.not_isSome_iff_eq_none.mp (by rw [h]; exact Bool.false_ne_true)

/-- **The narrowing law.** Take an item that the stored admission of the clause admits. No option
    that narrowing drops reads the item. Where the narrowed union is typed and guarded and its
    obligations hold, a write at a path whose frontier the narrowed union gives keeps the item
    readable by the union. -/
theorem narrow_law (hS : S.o.op = Orient.dual) {φ : Term S.sig} {os : List (Term S.sig)}
    {T : S.V → Prop} {μ : Option S.M} (hty : Typed α β (.union (narrow φ os)) T μ)
    (hob : Obligations α β (.union (narrow φ os))) (hg : (Term.union (narrow φ os)).guarded = true)
    (π : List Seg) (res : List (Frame S)) (hat : (Term.union (narrow φ os)).at π = some res)
    (w : S.C) (hw : ∀ g ∈ res, ∀ x a, w.e x = some a → ((Frame.sem α β g).p a).isSome)
    {A A' x a : S.V} (hφ : AdmA α β φ [] A = true) (hA : ((denote α β (.union os)).p A).isSome)
    (hx : w.e x = some a) (hput : putPath π a A = some A') :
    (∀ o ∈ os, o ∉ narrow φ os → (denote α β o).p A = none) ∧
      ((denote α β (.union os)).p A').isSome := by
  have hp : ∀ (c : S.C) (v : S.V), c.f S.o.op v = c.p v := fun c v => by rw [hS]
  refine ⟨fun o ho hd => ?_, ?_⟩
  · have h := narrow_drops (α := α) (β := β) ho hd [] hφ
    rw [AdmA_eq_isSome, hp] at h
    exact Option.not_isSome_iff_eq_none.mp (by rw [h]; exact Bool.false_ne_true)
  · have hA' : ((denote α β (.union (narrow φ os))).p A).isSome := by
      rw [← hp, narrow_reads φ os [] hφ, hp]; exact hA
    have h := strong_law hty hob hg π res hat w hw hA' hx hput
    replace h : (select (denoteList α β (narrow φ os) []) (·.p) A').isSome = true := h
    show (select (denoteList α β os []) (·.p) A').isSome = true
    rw [denoteList_eq] at h ⊢
    obtain ⟨c, hc, hcA⟩ := (select_isSome_attempt _ _ _).mp h
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hc
    exact (select_isSome_attempt _ _ _).mpr
      ⟨_, List.mem_map_of_mem (List.mem_filter.mp ho).1, hcA⟩

end Narrow

end Calculus.Alg
